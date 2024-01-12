open Core
open Opal

let (let*) = (>>=)

let count = ref 0
let fresh () = incr count; !count
let ctx : (string, int) Hashtbl.t = Hashtbl.create 10
let mk_var s =
  match Hashtbl.find_opt ctx s with
  | None ->
    let x = fresh () in
    Hashtbl.add ctx s x;
    x
  | Some x -> x

let parens x = between (exactly '(') (exactly ')') x
let integer = many1 digit => implode % int_of_string % (fun x -> Cst x)
let ident = (letter <~> many (exactly '_' <|> alpha_num)) => implode
let variable = ident => fun x -> Var (explode x)

let cbool = choice [
  token "true" >> return (Bcst true);
  token "false" >> return (Bcst false);
]

let add = token "+" >> spaces >> return (fun x y -> Add (x, y))
let sub = token "-" >> spaces >> return (fun x y -> Sub (x, y))
let mul = token "*" >> spaces >> return (fun _ -> assert false)
let div = token "/" >> spaces >> return (fun _ -> assert false)

let rec parse_expr input =
  chainl1 parse_term (add <|> sub) input
and parse_term input =
  chainl1 parse_factor (mul <|> div) input
and parse_factor input =
  choice [
    parens parse_expr;
    integer;
    variable
  ] input

let parse_comp =
  choice [
    token "<="  >> return (fun x y -> Ble (x, y));
    token "<"   >> return (fun x y -> Bnot (Ble (y, x)));
    token ">="  >> return (fun x y -> Ble (y, x));
    token ">"   >> return (fun x y -> Bnot (Ble (x, y)));
    token "="   >> return (fun x y -> Beq (x, y));
    token "!="  >> return (fun x y -> Bnot (Beq (x, y)));
  ]

let parse_cond =
  let* l = spaces >> parse_expr in
  let* c = spaces >> parse_comp in
  let* r = spaces >> parse_expr in
  return (c l r)

let band = token "and" >> spaces >> return (fun x y -> Band (x, y))
let bor = token "or" >> spaces >> return (fun x y -> Bnot (Band (Bnot x, Bnot y)))

let rec parse_bexpr input =
    chainl1 parse_bterm bor input
and parse_bterm input =
  chainl1 parse_bfactor band input
and parse_bfactor input =
  choice [
    parens parse_bexpr;
    cbool;
    parse_cond
  ] input

let to_seq = function
  | [] -> Skip
  | [x] -> x
  | x::xs -> List.fold_left (fun x y -> Seq (x, y)) x xs

let big_and = function
  | [] -> Bcst true
  | [x] -> x
  | x::xs -> List.fold_left (fun x y -> Band (x, y)) x xs

let parse_asssume =
  token "assume" >> spaces >> parse_bexpr

let parse_assert =
  token "assert" >> spaces >> parse_bexpr => (fun x -> Ite (x, Skip, Err))

let parse_prelude =
  many parse_asssume => big_and

let rec parse_prog input =
  (spaces >> (many parse_stmt => to_seq)) input
and parse_stmt input =
  (spaces >> (parse_if <|> parse_loop <|> parse_aff <|> parse_fail <|> parse_assert)) input
and parse_if input =
  begin
    let* _ = token "if" in
    let* c = spaces >> parse_bexpr in
    let* a = spaces >> between (token "{" << spaces) (token "}" << spaces) parse_prog in
    let* _ = token "else" in
    let* b = spaces >> between (token "{" << spaces) (token "}" << spaces) parse_prog in
    return (Ite (c, a, b))
  end input
and parse_loop input =
  begin
    let* _ = token "while" in
    let* c = spaces >> parse_bexpr in
    let* b = spaces >> between (token "{" << spaces) (token "}" << spaces) parse_prog in
    return (Loop (c, b))
  end input
and parse_aff input =
  begin
    let* x = (spaces >> ident) in
    let* _ = token "=" in
    let* e = spaces >> parse_expr in
    return (Asg (explode x, e))
  end input
and parse_fail input =
  (token "fail" >> return Err) input

let parse_unit =
  let* prelude = parse_prelude in
  let* body = parse_prog in
  return (prelude, body)

let parse_file f =
  let inx = open_in f in
  let stream = LazyStream.of_channel inx in
  match (parse_unit << spaces) stream with
  | Some (x, Nil) -> x
  | _ -> failwith "parse error"
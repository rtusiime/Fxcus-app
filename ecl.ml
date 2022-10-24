(*******************************************************************
    General-purpose LL(1) parser generator and parse tree generator,
    with syntax tree builder and (skeleton of a) translator for the
    extended calculator language.

    (c) Michael L. Scott, 2022
    For use by students in CSC 2/454 at the University of Rochester,
    during the Fall 2022 term.  All other use requires written
    permission of the author.

    If compiled and run, will execute "main()".
    Alternatively, can be "#use"-ed (or compiled and then "#load"-ed)
    into the top-level interpreter.

    Students: search for comments containing the word NOTICE.

 *******************************************************************)

open List;;
(* The List library includes a large collection of useful functions.
   In the provided code, I've used assoc, exists, filter, find,
   fold_left, hd, length, map, and rev.
*)

open Str;;      (* for regexp and split *)
(* The Str library provides a few extra string-processing routines.
   In particular, it provides "split" and "regexp", which I use to break
   program input into whitespace-separated words.  Note, however, that
   this library is not automatically available.  If you are using the
   top-level interpreter, you have to say
        #load "str.cma";;
   before you say
        #use "ecl.ml";;
   If you are generating an executable from the shell, you have to
   include the library name on the command line:
        ocamlc -o ecl str.cma ecl.ml
*)

(*******************************************************************
    Preliminaries.
 *******************************************************************)

(* Surprisingly, compose isn't built in.  It's included in various
   widely used commercial packages, but not in the core libraries. *)
let compose f g x = f (g x);;

type 'a stack = 'a list;;

(* is e a member of list l? *)
let member e l = exists ((=) e) l;;

(* OCaml has a built-in quicksort; this was just an exercise. *)
let rec sort l =
  let rec partition pivot l left right =
    match l with
    | []        -> (left, right)
    | c :: rest -> if c < pivot
                   then partition pivot rest (c :: left) right
                   else partition pivot rest left (c :: right) in
  match l with
  | []        -> l
  | h :: []   -> l
  | h :: rest -> let (left, right) = partition h rest [] [] in
                 (sort left) @ [h] @ (sort right);;

(* Leave only one of any consecutive identical elements in list. *)
let rec unique l =
  match l with
  | []             -> l
  | h :: []        -> l
  | a :: b :: rest -> if a = b (* structural eq *)
                      then unique (b :: rest)
                      else a :: unique (b :: rest);;

let unique_sort l = unique (sort l);;

(* Join two strings with a given separator in between
   -- but only if both are non-null. *)
let str_cat sep a b =
  match (a, b) with
  | (a, "") -> a
  | ("", b) -> b
  | (_, _) -> a ^ sep ^ b;;

(*******************************************************************
    Grammars, Parser Generator, Scanner, and Parser.

    For this course we are using a single grammar -- for the extended
    calcular language.  It was easiest for me to build the project,
    however, if I could experiment with changes to the language without
    having to change the parser by hand.  So we have here a complete
    parser generator.
 *******************************************************************)

type symbol_productions = (string * string list list);;
type grammar = symbol_productions list;;
type parse_table = (string * (string list * string list) list) list;;
(*                  nt        predict_set   rhs *)

let calc_gram : grammar =
  [ ("P",  [["SL"; "$$"]])
  ; ("SL", [["S"; "SL"]; []])
  ; ("S",  [ ["id"; ":="; "E"]; ["read"; "id"]; ["write"; "E"]])
  ; ("E",  [["T"; "TT"]])
  ; ("T",  [["F"; "FT"]])
  ; ("TT", [["AO"; "T"; "TT"]; []])
  ; ("FT", [["MO"; "F"; "FT"]; []])
  ; ("AO", [["+"]; ["-"]])
  ; ("MO", [["*"]; ["/"]])
  ; ("F",  [["id"]; ["num"]; ["("; "E"; ")"]])
  ];;

let ecg : grammar =
  [ ("P",  [["SL"; "$$"]])
  ; ("SL", [["S"; ";"; "SL"]; []])
  ; ("S",  [ ["int"; "id"; ":="; "E"]; ["real"; "id"; ":="; "E"]
           ; ["id"; ":="; "E"]; ["read"; "TP"; "id"]; ["write"; "E"]
           ; ["if"; "C"; "then"; "SL"; "end"]; ["while"; "C"; "do"; "SL"; "end"]
           ])
  ; ("TP", [["int"]; ["real"]; []])
  ; ("C",  [["E"; "RO"; "E"]])
  ; ("RO", [["=="]; ["<>"]; ["<"]; [">"]; ["<="]; [">="]])
  ; ("E",  [["T"; "TT"]])
  ; ("TT", [["AO"; "T"; "TT"]; []])
  ; ("T",  [["F"; "FT"]])
  ; ("FT", [["MO"; "F"; "FT"]; []])
  ; ("F",  [["id"]; ["i_num"]; ["r_num"]; ["("; "E"; ")"]
           ; ["trunc"; "("; "E"; ")"]; ["float"; "("; "E"; ")"]])
  ; ("AO", [["+"]; ["-"]])
  ; ("MO", [["*"]; ["/"]])
  ];;

(* Return all individual productions in grammar. *)
let productions gram : (string * string list) list =
  let prods (lhs, rhss) = map (fun rhs -> (lhs, rhs)) rhss in
  fold_left (@) [] (map prods gram);;

(* Return all symbols in grammar. *)
let gsymbols gram : string list =
  unique_sort
    (fold_left (@) [] (map (compose (fold_left (@) []) snd) gram));;

(* Return all elements of l that are not in to_exclude.
   Assume that both lists are sorted. *)
let list_minus l to_exclude =
  let rec helper rest te rtn =
    match rest with
    | []     -> rtn
    | h :: t -> match te with
                | []       -> (rev rest) @ rtn
                | h2 :: t2 -> match Stdlib.compare h h2 with
                              | -1 -> helper t te (h :: rtn)
                              |  0 -> helper t t2 rtn
                              |  _ -> helper rest t2 rtn in
  rev (helper l to_exclude []);;

(* Return just the nonterminals. *)
let nonterminals gram : string list = map fst gram;;

(* Return just the terminals. *)
let terminals gram : string list =
    list_minus (gsymbols gram) (unique_sort (nonterminals gram));;

(* Return the start symbol.  Throw exception if grammar is empty. *)
let start_symbol gram : string = fst (hd gram);;

let is_nonterminal e gram = member e (nonterminals gram);;

let is_terminal e gram = member e (terminals gram);;

let union s1 s2 = unique_sort (s1 @ s2);;

(* Return suffix of lst that begins with first occurrence of sym
   (or [] if there is no such occurrence). *)
let rec suffix sym lst = 
  match lst with
  | [] -> []
  | h :: t -> if h = sym (* structural eq *)
              then lst else suffix sym t;;

(* Return a list of pairs.
   Each pair consists of a symbol A and a list of symbols beta
   such that for some alpha, A -> alpha B beta. *)
type right_context = (string * string list) list;;
let get_right_context (b:string) gram : right_context =
  fold_left (@) []
            (map (fun prod ->
                    let a = fst prod in
                    let rec helper accum rhs =
                      let b_beta = suffix b rhs in
                      match b_beta with
                      | [] -> accum
                      | x :: beta  -> (* assert x = b *)
                                      helper ((a, beta) :: accum) beta in
                    helper [] (snd prod))
                 (productions gram));;

(********
    Parser generator starts here.
********)

type symbol_knowledge = string * bool * string list * string list;;
type knowledge = symbol_knowledge list;;
let symbol_field (s, e, fi, fo) = s;;
let eps_field (s, e, fi, fo) = e;;
let first_field (s, e, fi, fo) = fi;;
let follow_field (s, e, fi, fo) = fo;;

let initial_knowledge gram : knowledge =
  map (fun a -> (a, false, [], [])) (nonterminals gram);;

let get_symbol_knowledge (a:string) (kdg:knowledge) : symbol_knowledge =
  find (fun (s, e, fi, fo) -> s = a) kdg;;

(* Can word list w generate epsilon based on current estimates?
   if w is an empty list, yes
   if w is a single terminal, no
   if w is a single nonterminal, look it up
   if w is a non-empty list, "iterate" over elements *)
let rec generates_epsilon (w:string list) (kdg:knowledge) gram : bool =
  match w with
  | [] -> true
  | h :: t -> if is_terminal h gram then false
              else eps_field (get_symbol_knowledge h kdg)
                   && generates_epsilon t kdg gram;;

(* Return FIRST(w), based on current estimates.
   if w is an empty list, return []  [empty set]
   if w is a single terminal, return [w]
   if w is a single nonterminal, look it up
   if w is a non-empty list, "iterate" over elements *)
let rec first (w:string list) (kdg:knowledge) gram : (string list) =
  match w with
  | [] -> []
  | x :: _ when is_terminal x gram -> [x]
  | x :: rest -> let s = first_field (get_symbol_knowledge x kdg) in
                 if generates_epsilon [x] kdg gram
                 then union s (first rest kdg gram)
                 else s;;

let follow (a:string) (kdg:knowledge) : string list =
  follow_field (get_symbol_knowledge a kdg);;

let rec map3 f l1 l2 l3 =
  match (l1, l2, l3) with
  | ([], [], []) -> []
  | (h1 :: t1, h2 :: t2, h3 :: t3) -> (f h1 h2 h3) :: map3 f t1 t2 t3
  | _ -> raise (Failure "mismatched_lists in map3");;

(* Return knowledge structure for grammar.
   Start with (initial_knowledge grammar) and "iterate",
   until the structure doesn't change.
   Uses (get_right_context B gram), for all nonterminals B,
   to help compute follow sets. *)
let get_knowledge gram : knowledge =
  let nts : string list = nonterminals gram in
  let right_contexts : right_context list
     = map (fun s -> get_right_context s gram) nts in
  let rec helper kdg =
    let update : symbol_knowledge -> symbol_productions
                   -> right_context -> symbol_knowledge
          = fun old_sym_kdg sym_prods sym_right_context ->
      let my_first s = first s kdg gram in
      let my_eps s = generates_epsilon s kdg gram in
      let filtered_follow p = if my_eps (snd p)
                              then (follow (fst p) kdg)
                              else [] in
      (
        symbol_field old_sym_kdg,       (* nonterminal itself *)
        (eps_field old_sym_kdg)         (* previous estimate *)
            || (fold_left (||) false (map my_eps (snd sym_prods))),
        union (first_field old_sym_kdg) (* previous estimate *)
            (fold_left union [] (map my_first (snd sym_prods))),
        union (union
                (follow_field old_sym_kdg)  (* previous estimate *)
                (fold_left union [] (map my_first
                                      (map (fun p ->
                                              match snd p with
                                              | [] -> []
                                              | h :: t -> [h])
                                           sym_right_context))))
              (fold_left union [] (map filtered_follow sym_right_context))
      ) in    (* end of update *)
    let new_kdg = map3 update kdg gram right_contexts in
    (* body of helper: *)
    if new_kdg = kdg then kdg else helper new_kdg in
  (* body of get_knowledge: *)
  helper (initial_knowledge gram);;

let get_parse_table (gram:grammar) : parse_table =
  let kdg = get_knowledge gram in
  map (fun (lhs, rhss) ->
        (lhs, (map (fun rhs ->
                      (union (first rhs kdg gram)
                             (if (generates_epsilon rhs kdg gram)
                              then (follow lhs kdg) else []),
                      rhs))
                   rhss)))
      gram;;

type row_col = int * int;;      (* source location *)
let complaint (loc:row_col) (msg:string) =
  let (l, c) = loc in
  Printf.sprintf "line %d, col %d: %s" l c msg;;

(* Convert string to list of chars, each tagged with row and column. *)
let explode_and_tag (s:string) : (char * row_col) list =
  let rec exp i r c l =
    if i = String.length s then l
    else
      let (r2, c2) = if s.[i] = '\n' then (r+1, 1) else (r, c+1) in
      exp (i+1) r2 c2 ((s.[i], (r, c)) :: l) in
  rev (exp 0 1 1 []);;

(* Convert list of char to string.
   (This uses imperative features.  It used to be a built-in.) *)
let implode (l:char list) : string =
  let res = Bytes.create (length l) in
  let rec imp i l =
    match l with
    | [] -> Bytes.to_string res
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l;;

(********
   Scanner.  Currently specific to the extended calculator language.
********)

type token = string * string * row_col;;
(*         category * name   * row+column *)

let tokenize (program:string) : token list =
  let get_id prog =
    let rec gi tok p =
        match p with
        | (c, _) :: rest when (('a' <= c && c <= 'z')
                               || ('A' <= c && c <= 'Z')
                               || ('0' <= c && c <= '9') || (c = '_'))
            -> gi (c :: tok) rest
        | _ -> (implode (rev tok), p) in
    gi [] prog in
  let get_num prog =            (* eat digit* *)
    let get_int prog =
      let rec gi tok p =
          match p with
          | (c, _) :: rest when ('0' <= c && c <= '9')
              -> gi (c :: tok) rest
          | _ -> (implode (rev tok), p) in
      gi [] prog in
    let get_exp prog =          (* eat (e|E)(+|-|epsilon)digit+ *)
      match prog with
      | (e, eloc) :: r1 when (e = 'e' || e = 'E')
          -> (match r1 with
              | (s, _) :: (d, dloc) :: r2
                    when (s = '+' || s = '-') && ('0' <= d && d <= '9')
                -> let (pow, r3) = get_int ((d, dloc) :: r2) in
                   ((String.make 1 e) ^ (String.make 1 s) ^ pow, r3)
              | (d, dloc) :: r2 when ('0' <= d && d <= '9')
                -> let (pow, r3) = get_int ((d, dloc) :: r2) in
                   ((String.make 1 e) ^ pow, r3)
              | _ -> ("error", (e, eloc) :: r1))
      | _ -> ("", prog) in
    let (whole, r1) = get_int prog in
    match r1 with
    | ('.', _) :: r2
        -> let (frac, r3) = get_int r2 in
           let (exp, r4) = get_exp r3 in
           (whole ^ "." ^ frac ^ exp, r4)
    | _ -> (whole, r1) in
  let rec get_error tok prog =
    match prog with
    | [] -> (implode (rev tok), prog)
    | (c, _) :: rest ->
        match c with
        | ';' | ':' | '+' | '-' | '*' | '/' | '(' | ')'
        | '_'| '<' | '>' | '=' | 'a'..'z' | 'A'..'Z' | '0'..'9'
            -> (implode (rev tok), prog)
        | _ -> get_error (c :: tok) rest in
  let rec skip_space prog =
    match prog with
    | [] -> []
    | (c, _) :: rest -> if (c = ' ' || c = '\n' || c = '\r' || c = '\t')
                        then skip_space rest else prog in
  let rec tkize toks prog =
    match prog with
    | []                           -> ((("$$", (0, 0)) :: toks), [])
    | ('\n', _) :: rest
    | ('\r', _) :: rest
    | ('\t', _) :: rest
    | (' ', _)  :: rest            -> tkize toks (skip_space prog)
    | (':', l) :: ('=', _) :: rest -> tkize ((":=", l) :: toks) rest
    | (';', l) :: rest             -> tkize ((";", l)  :: toks) rest
    | ('+', l) :: rest             -> tkize (("+", l)  :: toks) rest
    | ('-', l) :: rest             -> tkize (("-", l)  :: toks) rest
    | ('*', l) :: rest             -> tkize (("*", l)  :: toks) rest
    | ('/', l) :: rest             -> tkize (("/", l)  :: toks) rest
    | ('(', l) :: rest             -> tkize (("(", l)  :: toks) rest
    | (')', l) :: rest             -> tkize ((")", l)  :: toks) rest
    | ('<', l) :: ('>', _) :: rest -> tkize (("<>", l) :: toks) rest
    | ('<', l) :: ('=', _) :: rest -> tkize (("<=", l) :: toks) rest
    | ('<', l) :: rest             -> tkize (("<", l)  :: toks) rest
    | ('>', l) :: ('=', _) :: rest -> tkize ((">=", l) :: toks) rest
    | ('>', l) :: rest             -> tkize ((">", l)  :: toks) rest
    | ('=', l) :: ('=', _) :: rest -> tkize (("==", l) :: toks) rest
    | (h, l) :: t ->
        match h with
        | '.' | '0'..'9' -> let (nm, rest) = get_num prog in
                            tkize ((nm, l) :: toks) rest
        | 'a'..'z'
        | 'A'..'Z'
        | '_'            -> let (nm, rest) = get_id prog in
                            tkize ((nm, l) :: toks) rest
        | x              -> let (nm, rest) = get_error [x] t in
                            tkize ((nm, l) :: toks) rest in
  let (toks, _) = (tkize [] (explode_and_tag program)) in
  let categorize tok =
    let (nm, loc) = tok in
    match nm with
    | "do"   | "end"   | "float" | "if"    | "int"   | "read"
    | "real" | "then"  | "trunc" | "while" | "write"
    | ";"    | ":="    | "+"     | "-"     | "*"     | "/"  | "(" | ")"
    | "<"    | "<="    | ">"     | ">="    | "<>"    | "==" | "$$"
        -> (nm, nm, loc)
    | _ -> match nm.[0] with
           | '.' -> (try 
                       if ('0' <= nm.[1] && nm.[1] <= '9')
                         then ("r_num", nm, loc)
                         else ("error", nm, loc)
                     with Invalid_argument(_) -> ("error", nm, loc))
           | '0'..'9' -> if String.contains nm '.'
                            then ("r_num", nm, loc)
                            else ("i_num", nm, loc)
           | 'a'..'z'
           | 'A'..'Z' | '_' -> ("id", nm, loc)
           | _ -> ("error", nm, loc) in
  map categorize (rev toks);;

(********
   Parser.  The main parse routine returns a parse tree (or PT_error if
   the input program is syntactically invalid).  To build that tree it
   employs a simplified version of the "attribute stack" described in
   Section 4.5.2 (pages 50-55) on the PLP companion site.
  
   When it predicts A -> B C D, the parser pops A from the parse stack
   and then, before pushing D, C, and B (in that order), it pushes a
   number (in this case 3) indicating the length of the right hand side.
   It also pushes A into the attribute stack.
  
   When it matches a token, the parser pushes this into the attribute
   stack as well.
  
   Finally, when it encounters a number (say k) in the stack (as opposed
   to a character string), the parser pops k+1 symbols from the
   attribute stack, joins them together into a list, and pushes the list
   back into the attribute stack.
  
   These rules suffice to accumulate a complete parse tree into the
   attribute stack at the end of the parse.
  
   Note that everything is done functionally.  We don't really modify
   the stacks; we pass new versions to tail recursive routines.
********)

(* Extract grammar from parse-tab, so we can invoke the various routines
   that expect a grammar as argument. *)
let grammar_of (parse_tab:parse_table) : grammar =
  map (fun p -> (fst p,
                 (fold_left (@)
                            []
                            (map (fun (a, b) -> [b]) (snd p)))))
      parse_tab;;

type parse_tree =   (* among other things, parse_trees are *)
| PT_error          (* the elements of the attribute stack *)
| PT_id of (string * row_col)
| PT_int of (string * row_col)
| PT_real of (string * row_col)
| PT_term of (string * row_col)
| PT_nt of (string * row_col * parse_tree list);;
    
(* Pop rhs-len + 1 symbols off the attribute stack,
   assemble into a production, and push back onto the stack. *)
let reduce_1_prod (astack:parse_tree list) (rhs_len:int) : parse_tree list =
  let rec helper atk k prod =
    match (k, atk) with
    | (0, PT_nt(nt, loc, []) :: t) -> PT_nt(nt, loc, prod) :: t
    | (n, h :: t) when n <> 0 -> helper t (k - 1) (h :: prod)
    | _ -> raise (Failure "expected nonterminal at top of astack") in
   helper astack rhs_len [];;

type parse_action = PA_error | PA_prediction of string list;;
(* Double-index to find prediction (list of RHS symbols) for
   nonterminal nt and terminal t.
   Return PA_error if not found. *)
let get_parse_action (nt:string) (t:string) (parse_tab:parse_table)
    : parse_action =
  let rec helper l =
      match l with
      | [] -> PA_error
      | (fs, rhs) :: rest -> if member t fs then PA_prediction(rhs)
                             else helper rest in
  helper (assoc nt parse_tab);;

type ps_item =
| PS_end of int
| PS_sym of string;;

(* Parse program according to grammar.
   [Commented-out code would
       print predictions and matches (imperatively) along the way.]
   Return parse tree if the program is in the language; PT_error if it's not. *)
let parse (parse_tab:parse_table) (program:string) : parse_tree =
  let die loc msg =
    begin
      let (l, c) = loc in
      (* print to screen in REPL; to stderr when compiled *)
      (if !Sys.interactive then Printf.printf else Printf.eprintf)
        "syntax error at line %d, col %d: %s\n" l c msg;
      PT_error 
    end in
  let gram = grammar_of parse_tab in
  let rec helper pstack tokens astack =
    match pstack with
    | [] ->
        if tokens = [] then
          (* assert: astack is nonempty *)
          hd astack
        else die (0, 0) "extra input beyond end of program"
    | PS_end(n) :: ps_tail ->
        helper ps_tail tokens (reduce_1_prod astack n)
    | PS_sym(tos) :: ps_tail ->
        match tokens with
        | [] -> die (0, 0) "unexpected end of program"
        | (term, nm, loc) :: more_tokens ->
           (* if nm is an individual identifier or number,
              term will be a generic "id" or "i_num" or "r_num" *)
          if is_terminal tos gram then
            if tos = term then
              begin
              (*
                print_string ("   match " ^ tos);
                print_string
                    (if tos <> term      (* value comparison *)
                         then (" (" ^ nm ^ ")") else "");
                print_newline ();
              *)
                helper ps_tail more_tokens
                       (( match term with
                          | "id"  -> PT_id(nm, loc)
                          | "i_num" -> PT_int(nm, loc)
                          | "r_num" -> PT_real(nm, loc)
                          | _     -> PT_term(nm, loc) ) :: astack)
              end
                       (* note push of nm into astack *)
            else die loc ("expected " ^ tos ^ " ; saw " ^ nm)
          else (* nonterminal *)
            match get_parse_action tos term parse_tab with
            | PA_error -> die loc ("no prediction for " ^ tos
                                   ^ " when seeing " ^ nm)
            | PA_prediction(rhs) ->
                begin
                (*
                  print_string ("   predict " ^ tos ^ " ->");
                  print_string (fold_left (fun a b -> a ^ " " ^ b) "" rhs);
                  print_newline ();
                *)
                  helper ((fold_left (@) [] 
                                    (map (fun s -> [PS_sym(s)]) rhs))
                              @ [PS_end(length rhs)] @ ps_tail)
                         tokens (PT_nt(tos, loc, []) :: astack)
                end in
  helper [PS_sym(start_symbol gram)] (tokenize program) [];;

let cg_parse_table = get_parse_table calc_gram;;

let ecg_parse_table = get_parse_table ecg;;

(*******************************************************************
    (* NOTICE *)

    Everything above this point in the file is complete and (I think)
    usable as-is.  The rest of the file, from here down, is a possible
    skeleton for the code you need to write.  It was extracted from
    the complete working version available as ~cs254/bin/ecl on the csug
    machines.

 *******************************************************************)

(* Syntax tree node types.
   We distinguish between statements and expressions. *)
type ast_sl = ast_s list
and ast_s =
| AST_error
| AST_i_dec of (string * row_col)       (* id location  [AST_i_dec("int",id_loc); AST_id(id,id_loc)] -> [AST_i_dec(id,id_loc)] *)
| AST_r_dec of (string * row_col)       (* id location *)
| AST_read of (string * row_col)        (* id location *)
| AST_write of (ast_e)
| AST_assign of (string * ast_e * row_col * row_col)
                             (* id location, := location *)
| AST_if of (ast_e * ast_sl)
| AST_while of (ast_e * ast_sl)
and ast_e =
| AST_int of (string * row_col)
| AST_real of (string * row_col)
| AST_id of (string * row_col)
| AST_float of (ast_e * row_col)        (* lparen location *)
| AST_trunc of (ast_e * row_col)        (* lparen location *)
| AST_binop of (string * ast_e * ast_e * row_col);;
                                        (* op location *)
                                     
(* Convert parse tree to syntax tree.
   Walks the parse tree using a collection of mutually recursive subroutines. *)
let rec ast_ize_prog (p:parse_tree) : ast_sl =
  match p with
  | PT_nt("P",_,[st_list; PT_term("$$",_)])
    -> ast_ize_stmt_list st_list 
  | _ -> raise (Failure "malformed parse tree in ast_ize_prog")

and ast_ize_stmt_list (sl:parse_tree) : ast_sl =
  match sl with
  | PT_nt("SL", _, []) -> []            (* end of list *)
  | PT_nt("SL", _, [st; PT_term(";", _); st_list])
    -> append (ast_ize_stmt st) (ast_ize_stmt_list st_list)
  | _ -> raise (Failure "malformed parse tree in ast_ize_stmt_list")

and ast_ize_stmt (s:parse_tree) : ast_sl =
  match s with
  | PT_nt("S", _, [PT_id(lhs, vloc); PT_term(":=", aloc); expr])
      -> [AST_assign(lhs, (ast_ize_expr expr), vloc, aloc)]
         (* vloc (Value Location)is the place to complain about undeclared lhs;
            aloc (Assign Location) (:= sign) is the place to complain about a type clash *)
  (* int id := expr *)
  | PT_nt("S", _, [PT_term("int",dloc); PT_id(lhs, vloc); PT_term(":=", aloc); expr])
    -> [AST_i_dec(lhs,vloc); AST_assign(lhs, (ast_ize_expr expr), vloc, aloc)]
  (* real id := expr *)
  | PT_nt("S", _, [PT_term("real",dloc); PT_id(lhs, vloc); PT_term(":=", aloc); expr])
    -> [AST_r_dec(lhs,vloc); AST_assign(lhs, (ast_ize_expr expr), vloc, aloc)]
  (* read TP id *)
  (* NOT SURE ABOUT THIS, NEED REVISION *)
  | PT_nt("S", _, [PT_term("read",rloc); PT_nt("TP",_,[PT_term("int",tploc)]); PT_id(id,idloc)])
    -> [AST_i_dec(id,idloc); AST_read(id,idloc)]
  | PT_nt("S", _, [PT_term("read",rloc); PT_nt("TP",_,[PT_term("real",tploc)]); PT_id(id,idloc)])
    -> [AST_r_dec(id,idloc); AST_read(id,idloc)]
  (* write E *)
  | PT_nt("S", _, [PT_term("write",wloc); expr])
    -> [AST_write((ast_ize_expr expr))]
  (* if C then SL end *)
  | PT_nt("S", _, [PT_term("if",_); cond; PT_term("then", _); sl; PT_term("end",_)])
    -> [AST_if((ast_ize_cond cond),(ast_ize_stmt_list sl))]
  (* while C then SL end *)
  | PT_nt("S", _, [PT_term("while",_); cond; PT_term("do", _); sl; PT_term("end",_)])
    -> [AST_while((ast_ize_cond cond),(ast_ize_stmt_list sl))]
  | _ -> raise (Failure "malformed parse tree in ast_ize_stmt")

and ast_ize_expr (e:parse_tree) : ast_e =   (* C, E, T, or F *)
  match e with
  | PT_nt("E",_,[term; term_tail]) 
    -> ast_ize_expr_tail (ast_ize_expr term) term_tail
  | PT_nt("T",_,[factor; factor_tail]) 
    -> ast_ize_expr_tail (ast_ize_expr factor) factor_tail
    (* id *)
  | PT_nt("F",_, [PT_id(v, vloc)]) 
    -> AST_id(v,vloc)
    (* int  or i_num *)
  | PT_nt("F",_, [PT_int(nm, nmloc)]) 
    -> AST_int(nm,nmloc)
    (* real or r_num *)
  | PT_nt("F",_, [PT_real(nm, nmloc)]) 
    -> AST_real(nm,nmloc)
    (* ( expr ) *)
  | PT_nt("F",_, [PT_term("(",_); expr; PT_term(")",_)]) 
    -> (ast_ize_expr expr)
        (* float ( expr ) *)
  | PT_nt("F",_, [PT_term("float",floc); PT_term("(",_); expr; PT_term(")",_)]) 
    -> AST_float((ast_ize_expr expr),floc)
        (* trunc ( expr ) *)
  | PT_nt("F",_, [PT_term("trunc",tloc); PT_term("(",_); expr; PT_term(")",_);]) 
    -> AST_trunc((ast_ize_expr expr),tloc) (* NOT SURE ABOUT THIS *)
  | _ -> raise (Failure "malformed parse tree in ast_ize_expr")

and ast_ize_expr_tail (lhs:ast_e) (tail:parse_tree) : ast_e =   (* ET,TT, or FT *)
  match tail with
    | PT_nt ("TT", _, []) -> lhs     (* end of list *)
    | PT_nt("FT", _, []) -> lhs          (* end of list *)
    | PT_nt("TT",_,[PT_nt("AO",_,[PT_term(ao,oploc)]); term; term_tail]) 
      -> AST_binop(ao, lhs, (ast_ize_expr_tail (ast_ize_expr term) term_tail), oploc)
    | PT_nt("FT",_,[PT_nt("MO",_,[PT_term(mo,oploc)]); term; term_tail]) 
      -> AST_binop(mo, lhs, (ast_ize_expr_tail (ast_ize_expr term) term_tail), oploc)
    | _ -> raise (Failure "malformed parse tree in ast_ize_expr_tail")

and ast_ize_cond (c:parse_tree) : ast_e =
  match c with
  | PT_nt("C",_,[lexpr; PT_nt("RO",_,[PT_term(ro,roloc)]); rexpr])
    -> AST_binop(ro, (ast_ize_expr lexpr), (ast_ize_expr rexpr), roloc)
  | _ -> raise (Failure "malformed parse tree in ast_ize_cond")
;;

(*******************************************************************
    AST Pretty-printer.

    NOTICE: this is the code of the ast_gen tool we gave you for A2.

 *******************************************************************)

let rec pp_sl (sl:ast_sl) (ind:string) : string =
  match sl with
  | []      -> ""
  | [s]     -> pp_s s ind
  | s :: tl -> pp_s s ind ^ "\n" ^ ind ^ pp_sl tl ind

and pp_s (s:ast_s) (ind:string) : string =
  match s with
  | AST_i_dec(id, _)           -> "(int \"" ^ id ^ "\")"
  | AST_r_dec(id, _)           -> "(real \"" ^ id ^ "\")"
  | AST_read(id, _)            -> "(read \"" ^ id ^ "\")"
  | AST_write(expr)            -> "(write " ^ (pp_e expr) ^ ")"
  | AST_assign(id, expr, _, _) -> "(:= \"" ^ id ^ "\" " ^ pp_e expr ^ ")"
  | AST_if(cond, sl)           -> "(if " ^ (pp_e cond)
                                   ^ "\n" ^ ind ^ "  [ "
                                   ^ (pp_sl sl (ind ^ "    "))
                                   ^ "\n" ^ ind ^ "  ]\n" ^ ind ^ ")"
  | AST_while(cond, sl)        -> "(while " ^ (pp_e cond)
                                   ^ "\n" ^ ind ^ "  [ "
                                   ^ (pp_sl sl (ind ^ "    "))
                                   ^ "\n" ^ ind ^ "  ]\n" ^ ind ^ ")"
  | AST_error                   -> "error"

and pp_e (e:ast_e) : string =
  match e with
  | AST_int(num, _)          -> "\"" ^ num ^ "\""
  | AST_real(num, _)         -> "\"" ^ num ^ "\""
  | AST_id(id, _)            -> "\"" ^ id ^ "\""
  | AST_float(e, _)          -> "(float " ^ (pp_e e) ^ ")"
  | AST_trunc(e, _)          -> "(trunc " ^ (pp_e e) ^ ")"
  | AST_binop(op, lo, ro, _) -> "(" ^ op ^ " " ^ pp_e lo ^ " " ^ pp_e ro ^ ")"

let pp_p (sl:ast_sl) = print_string ("[ " ^ (pp_sl sl "  ") ^ "\n]\n")

(*******************************************************************
    Static checker and translator for AST.

    Generate code corresponding to a given AST.  Catch undefined
    variables, redefinitions, and type clashes.  Respect scopes: each
    variable should be visible from its declaration to the end of the
    innermost statement list in which it is declared.

    The calculator language is simple enough that static checking and
    code generation can be performed in a single depth-first
    left-to-right traversal of the AST.  (This would not be the case in
    more complicated languages.)  A nice side effect of doing a single
    traversal is that semantic error messages can simple be accumulated
    in a list, without the need to subsequently sort by line and column
    number.
    
    Significant amounts of information can be carried along in the
    traversal using parameter and return values of type symtab (symbol
    table).  When errors are encountered, further code generation can
    be disabled but additional errors should be accumulated.
 *******************************************************************)

(********
    Symbol table.  Principal component is a stack of scopes.
    In turn, principal component of a scope is a list of (id, type,
    address) triples.  

    NOTICE: both scope and main symbol table can be augmented with
    additional fields to manage the use of labels and of memory
    (i and r) and temporary (ti and tr) slots ("registers").
********)

(* Variables my be integers or reals.  If we use an undeclared variable,
   we put it in the table with type "Unknown" to disable subsequent "not
   found" messages. *)
type tp = Int | Real | Unknown;;
type scope_info =
  { (*
        NOTICE: extra field(s) here?
    *)
    variables : (string * tp * int) list
  };;
type symtab =
  { (*
        NOTICE: extra field(s) here?
    *)
    scopes     : scope_info list
  };;
let empty_symtab = { scopes = [] };;

(* Open a new scope, in which variable names can be reused. *)
let new_scope (st:symtab) : symtab =
  { scopes     = { variables = [] } :: st.scopes };;

(* Executed at end of statement list to erase variables from table. *)
let end_scope (st:symtab) : symtab =
  let ss = match st.scopes with
           | []            -> raise (Failure "no scopes left to pop")
           | _ :: surround -> surround in
  { scopes     = ss }

(* An expression in the extended calculator language can appear
   - as an operand in a bigger expression -- arithmetic, comparison, float/trunc
   - on the RHS of an assignment
   - in a write statement

   Somewhat arbitrarily, we're decreeing that in our pidgin C output the
   RHS of an assignment can include no more than one operator, and in all
   other contexts an expression must be a variable, constant, or temporary.

   Temporaries (our surrogate registers) are (in this simple compiler)
   allocated in stack order.  
*)
type okind =
    | Atom          (* variable or constant *)
    | Temp of int;; (* "register" number *)
type operand =
  { text : string;
    kind : okind
  };;

(* Identify triple corresponding to an id. *)
let name_match_st id = fun (sym, _, _) -> id = sym;;

(*
    NOTICE: you will need a better (correct) way to allocate memory
    addresses for variables.  These routines are placeholders for
    functionality that you probably want to roll into the symbol table.
*)
let new_mem_addr () = 0;;
let max_mem_addr () = 0;;
let max_temp_addr () = 0;;

(* Insert id with type t and a newly chosen address into current scope
   in symbol table if not already present; return updated symtab and
   indication of success *)
let insert_st (id:string) (t:tp) (st:symtab) : symtab * bool =
  match st.scopes with
  | [] -> raise (Failure "no current scope in which to insert")
  | scope :: surround ->
      match find_opt (name_match_st id) scope.variables with
      | Some _ -> (st, false)
      | None   ->
          ({ scopes     =
               { variables = (id, t, new_mem_addr ()) :: scope.variables }
               :: surround }, true);;

(* Look id up in symbol table.  If not found, insert to limit redundant
   subsequent errors. *)
let lookup_st (id:string) (st:symtab) (loc:row_col)
    : tp * string * string * symtab =
    (* type, target-code name, error msg, new symtab *)
  let rec helper scope_stack =
    match scope_stack with
    | [] -> let (new_st, stat) = (insert_st id Unknown st) in
            if stat then (Unknown, "", (complaint loc (id ^ " not found")), new_st)
                    else raise (Failure (id ^ " found but unexpected")) 
    | scope :: surround ->
        match find_opt (name_match_st id) scope.variables with
        | Some (_, t, a) ->
           (match t with
            | Int     -> (t, ("i[" ^ Int.to_string a ^ "]"), "", st)
            | Real    -> (t, ("r[" ^ Int.to_string a ^ "]"), "", st)
            | Unknown -> (t, "", "", st))   (* already complained *)
        | None -> helper surround in
  helper st.scopes;;

(********
    Utility routines assumed available by translated code.
********)

let prologue = "\
#include <stdio.h>\n\
#include <stdlib.h>\n\
\n\
int64_t getint() {\n\
    int64_t rtn;\n\
    switch (scanf(\"%lld\", &rtn)) {\n\
        case EOF:\n\
            fprintf(stderr, \"unexpected end of file\\n\");\n\
            exit(1);\n\
        case 0:\n\
            fprintf(stderr, \"unexpected non-numeric input\\n\");\n\
            exit(1);\n\
        case 1: break;\n\
    }\n\
    return rtn;\n\
}\n\
\n\
void putint(int64_t x) {\n\
    printf(\"%lld\\n\", x);\n\
}\n\
\n\
double divide_int(int64_t n, int64_t d) {\n\
    if (d == 0) {\n\
        fprintf(stderr, \"divide by zero\\n\");\n\
        exit(1);\n\
    }\n\
    return n/d;\n\
}\n\
\n\
int getreal() {\n\
    double rtn;\n\
    switch (scanf(\"%lf\", &rtn)) {\n\
        case EOF:\n\
            fprintf(stderr, \"unexpected end of file\\n\");\n\
            exit(1);\n\
        case 0:\n\
            fprintf(stderr, \"unexpected non-numeric input\\n\");\n\
            exit(1);\n\
        case 1: break;\n\
    }\n\
    return rtn;\n\
}\n\
\n\
void putreal(double x) {\n\
    printf(\"%lg\\n\", x);\n\
}\n\
\n\
double divide_real(double n, double d) {\n\
    if (d == 0) {\n\
        fprintf(stderr, \"divide by zero\\n\");\n\
        exit(1);\n\
    }\n\
    return n/d;\n\
}\n\
\n\
double to_real(int64_t n) {return (double) n;}\n\
int64_t to_int(double x) {return (int64_t) x;}\n\
\n\
int main() {\n\
";;

(********
    Actual translator.
********)

(* Like most of the translate_X routines, translate_sl accumulates code
   and error messages into string lists.  We stitch these together with
   intervening carriage returns at the end, in translate_ast. *)
(* let id_check (id: string) (is_dec: bool) (loc: row_col) (st:symtab) *)
(* KEV *)
(* let type_clash_check *)
(* ET *)
(* let unary_check *)
(* ET *)

let rec translate_sl (sl:ast_sl) (st:symtab)
    : symtab * string list * string list =
    (* new symtab, code, error messages *)
  match sl with
  | [] -> (st, [], [])    (* empty statement list *)
  | s :: rest ->
      let (st2, s_code, s_errs) = translate_s s st in
      let (st3, sl_code, sl_errs) = translate_sl rest st2 in
      let errs = s_errs @ sl_errs in
      if errs = [] then (st3, s_code @ sl_code, [])
      else (st3, [], errs)

and translate_s (s:ast_s) (st:symtab)
    : (symtab * string list * string list) =
    (* new symtab, code, error messages *)
  match s with
  | AST_i_dec(id,idloc) ->   let (new_st, inserted) = (insert_st id Int st) in
                             let (rw, col) = idloc in
                             if inserted then (new_st, ["int"], [""])
                             else (new_st, [""],["redifinition of " ^id ^ " at "^(string_of_int rw) ^ " "^ (string_of_int col) ])
  | AST_r_dec(id,idloc) ->   let (new_st, inserted) = (insert_st id Real st) in
                             if inserted then (new_st, ["real"], [""])
                             else (new_st, [""],["redifinition of " ^id ^ " "^(string_of_int rw) ^ " "^ (string_of_int col)])
  | AST_read(id, idloc) ->   translate_read id idloc st
  | AST_write(expr)     ->   translate_write expr st
  | AST_if(expr , sl)   ->   translate_if expr sl st
  | AST_while(expr, sl) ->   translate_while expr sl st
  | _ -> st, [], []

  (* read type id *)
  (* 1. id is never declared -> insert id into symtable *)
  (* 2. id is declared in current scope -> complaint, diable translation*)
  (* 3. id is declared in the surround scope, bind the variable in the current scope, and leave the original binding untouch *)
  (* read id *)
  (* 1. id is declared -> do nothing *)
  (* 2. id is declared before -> complaint, diable translation*)
and translate_read (id:string) (loc:row_col) (* of variable *) (st:symtab)
    : symtab * string list * string list =
    (* new symtab, code, error messages *)
  let (typ, targ_code, err_msg, sym_tab) = lookup_st id st loc in
  match typ with
  | Unknown -> (sym_tab, [""], err_msg) 
  | _       -> (sym_tab, [targ_code], [""])

and translate_write (expr:ast_e) (st:symtab)
    : symtab * string list * string list =
    (* new symtab, code, error messages *)
  let (new_st, typ, setup_code , oper, err_msg) = translate_expr expr st in
    (st, setup_code, err_msg)
(* END KEV *)


(* BEGIN ET *)
and translate_assign (id:string) (rhs:ast_e) (vloc:row_col) (aloc:row_col) (st:symtab)
    : symtab * string list * string list =
    (* new symtab, code, error messages *)
  (*
    NOTICE: your code here
  *)
  (st, [], [])

and translate_if (c:ast_e) (sl:ast_sl) (st:symtab)
    : symtab * string list * string list =
    (* new symtab, code, error messages *)
    (* NEED ID CHECK *)
    (* NEED OPERAND CHECK  *)
  match c with      (* sanity check *)
  | AST_binop(_, _, _, _) ->
  (*
    NOTICE: your code here
  *)
      (st, [], [])
  | _ -> raise (Failure "unexpected expression type as condition")

and translate_while (c:ast_e) (sl:ast_sl) (st:symtab)
    : symtab * string list * string list =
    (* new symtab, code, error messages *)
  (*
    NOTICE: your code here
  *)
  (st, [], [])

and translate_expr (expr:ast_e) (st:symtab)
    : symtab * tp * string list * operand * string list =
    (* new symtab, type, setup code, self, error messages *)
  match expr with
  | AST_int(i, _)            -> (st, Int, [], {text = i; kind = Atom}, [])
  (*
    NOTICE: your code here
  *)
  | _ -> (st, Unknown, [], {text = ""; kind = Atom}, [])
(* END ET *)
(* Perform static checks on AST.  Return output code and error messages as
   glued-together strings.  Empty error string means tree was error free. *)
let translate_ast (ast:ast_sl) : int * int * string * string =
                               (* max_addr, max_temp, code, error messages *)
  let (st, sl_code, sl_errs) = translate_sl ast (new_scope empty_symtab) in
  ( max_mem_addr (), max_temp_addr (),
    (fold_left (str_cat "\n ") "" sl_code),
    (fold_left (str_cat "\n ") "" sl_errs) );;

(*******************************************************************
    Testing
 *******************************************************************)

let sum_ave_prog = "
    read int a; read int b; int sum := a + b;
    write sum; write float(sum) / 2.0;";;

let primes_prog = "
    read int n;
    int cp := 2 ;
    while n > 0 do
        int found := 0 ;
        int cf1 := 2 ;
        int cf1s := cf1 * cf1 ;
        while cf1s <= cp do
            int cf2 := 2 ;
            int pr := cf1 * cf2 ;
            while pr <= cp do
                if pr == cp then
                    found := 1 ;
                end ;
                cf2 := cf2 + 1 ;
                pr := cf1 * cf2 ;
            end ;
            cf1 := cf1 + 1 ;
            cf1s := cf1 * cf1 ;
        end ;
        if found == 0 then
            write cp ;
            n := n - 1 ;
        end ;
        cp := cp + 1 ;
    end ;";;

let gcd_prog = "
    read int a;
    read int b;
    while a <> b do
        if a > b then
            a := a - b;
        end;
        if b > a then
            b := b - a;
        end;
        if a == b then
            write a;
        end;
    end;";;

let sqrt_prog = "
    read real d;
    real l := d / 2.0;
    while l * l > d do
        l := l / 2.0;
    end;
    real h := 2.0 * l;
    real err := d - (l * l);
    if err < 0.0 then err := 0.0 - err; end;
    while err > 1.e-10 do
        real a := (l + h) / 2.0;
        if (a * a) < d then l := a; end;
        if (a * a) > d then h := a; end;
        err := d - (l * l);
        if err < 0.0 then err := 0.0 - err; end;
    end;
    write l;";;


let ecg_ast prog = ast_ize_prog (parse ecg_parse_table prog);;  
let ecg_code prog = translate_ast (ecg_ast prog);; 

let sum_ave_parse_tree = parse ecg_parse_table sum_ave_prog;;
let sum_ave_syntax_tree = ast_ize_prog sum_ave_parse_tree;;

let gcd_parse_tree = parse ecg_parse_table gcd_prog;;
let gcd_syntax_tree = ast_ize_prog gcd_parse_tree;;

let primes_parse_tree = parse ecg_parse_table primes_prog;;
let primes_syntax_tree = ast_ize_prog primes_parse_tree;;

let sqrt_parse_tree = parse ecg_parse_table sqrt_prog;;
let sqrt_syntax_tree = ast_ize_prog sqrt_parse_tree;;

let main () =

  (* This loop is imperative, but you're allowed to leave it as is. *)
  let lines = ref [] in
    try
      while true do
        lines := read_line () :: !lines;
      done
    with
      End_of_file ->
        let prog = String.concat "\n" (rev !lines) in
        let (max_addr, max_temp, code, errs) = ecg_code prog in
        if errs <> "" then
          Printf.eprintf " %s\n" errs
        else
          begin
            print_string prologue;
            Printf.printf " int64_t i[%d]; double *r = (double *) i;\n"
                          (max_addr + 1);
            Printf.printf " int64_t ti[%d]; double *tr = (double *) ti;\n\n"
                          (max_temp + 1);
            Printf.printf " %s\n}\n" code;
          end;;

(* Execute function "main" iff run as a stand-alone program. *)
if !Sys.interactive then () else main ();;


let p = "a:=1;";;
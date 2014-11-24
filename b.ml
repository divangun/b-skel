(*
   B Interpreter
*)
(* Location : don't mention it *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M(Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c::t else h::(replace_nth t (n-1) c)
    | [] -> raise Not_allocated

  let load (M(boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V(v) -> v 
    | U -> raise Not_initialized

  let store (M(boundary,storage)) loc content =
    M(boundary, replace_nth storage (Loc.diff boundary loc) (V(content)))

  let alloc (M(boundary,storage)) = (boundary,M(Loc.increase boundary 1,U::storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E(fun x -> raise Not_bound)
  let lookup (E(env)) id = env id
  let bind (E(env)) id loc = E(fun x -> if x = id then loc else env x)
end



(*
 * B Interpreter
 *)
module type B_TYPE =
sig
  exception Error of string
  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp            (* sequence *)
  | IF of exp * exp * exp       (* if-then-else *)
  | WHILE of exp * exp          (* while loop *)
  | LETV of id * exp * exp      (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list      (* call by value *)
  | CALLR of id * id list       (* call by referenece *)
  | RECORD of (id * exp) list   (* record construction *)
  | FIELD of exp * id           (* access record field *)
  | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module B : B_TYPE =
struct
  exception Error of string

  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp 
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp            (* sequence *)
  | IF of exp * exp * exp       (* if-then-else *)
  | WHILE of exp * exp          (* while loop *)
  | LETV of id * exp * exp      (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list      (* call by value *)
  | CALLR of id * id list       (* call by referenece *)
  | RECORD of (id * exp) list   (* record construction *)
  | FIELD of exp * id           (* access record field *)
  | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp

  type program = exp

  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v = 
    match v with 
    | Num n -> n
    | Bool _ -> raise (Error "Bool type is used as Num type")
    | Unit -> raise (Error "Unit type is used as Num type")
    | Record _ -> raise (Error "Unit type is used as Num type")

  let value_bool v =
    match v with
    | Bool b -> b
    | Num _ -> raise (Error "Num type is used as Bool type")
    | Unit -> raise (Error "Unit type is used as Bool type")
    | Record _ -> raise (Error "Unit type is used as Bool type")

    let value_unit v =
    match v with 
    | Unit -> ()
    | Num _ -> raise (Error "Num type is used as Unit type")
    | Bool _ -> raise (Error "Bool type is used as Unit type")
    | Record _ -> raise (Error "Bool type is used as Unit type")

  let value_record v =
    match v with
    | Record r -> r
    | Num _ -> raise (Error "Num type is used as Record type")
    | Unit -> raise (Error "Unit type is used as Record type")
    | Bool _ -> raise (Error "Bool type is used as Record type")

  let env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "not allowed")) 
    with Env.Not_bound -> raise (Error "not bound")

  let env_proc e f =
    try
      (match Env.lookup e f with
        | Addr _ -> raise (Error "not allowed") 
      | Proc (id, exp, env) -> (id, exp, env))
    with Env.Not_bound -> raise (Error "not bound")
      
  let rec eval : memory -> env -> exp -> (value * memory) = 
    fun mem env e -> match e with
    | NUM i -> (Num i, mem)
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | UNIT -> (Unit, mem)
    | VAR x -> (Mem.load mem (env_loc env x), mem)
    | ADD (e1, e2) ->
      (match (eval mem env e1) with
        | (Num n1, mem1) ->
          (match (eval mem1 env e2) with
            | (Num n2, mem2) -> (Num (n1+n2), mem2)
            | (Bool _, _) -> raise(Error "ADD : Expected int type of value, but bool type supplied")
            | (Unit, _) -> raise (Error "ADD : Expected int type of value, but unit type supplied")
            | (Record _,_) -> raise (Error "ADD : Expected int type of value, but record type supplied"))
        | (Bool _, _) -> raise(Error "ADD : Expected int type of value, but bool type supplied")
        | (Unit, _) -> raise (Error "ADD : Expected int type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "ADD : Expected int type of value, but record type supplied"))
    | SUB (e1, e2) ->
      (match (eval mem env e1) with
        | (Num n1, mem1) ->
          (match (eval mem1 env e2) with
            | (Num n2, mem2) -> (Num (n1-n2), mem2)
            | (Bool _, _) -> raise(Error "SUB : Expected int type of value, but bool type supplied")
            | (Unit, _) -> raise (Error "SUB : Expected int type of value, but unit type supplied")
            | (Record _,_) -> raise (Error "SUB : Expected int type of value, but record type supplied"))
        | (Bool _, _) -> raise(Error "SUB : Expected int type of value, but bool type supplied")
        | (Unit, _) -> raise (Error "SUB : Expected int type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "SUB : Expected int type of value, but record type supplied"))
    | MUL (e1, e2) ->
      (match (eval mem env e1) with
        | (Num n1, mem1) ->
          (match (eval mem1 env e2) with
            | (Num n2, mem2) -> (Num (n1*n2), mem2)
            | (Bool _, _) -> raise(Error "MUL : Expected int type of value, but bool type supplied")
            | (Unit, _) -> raise (Error "MUL : Expected int type of value, but unit type supplied")
            | (Record _,_) -> raise (Error "MUL : Expected int type of value, but record type supplied"))
        | (Bool _, _) -> raise(Error "MUL : Expected int type of value, but bool type supplied")
        | (Unit, _) -> raise (Error "MUL : Expected int type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "MUL : Expected int type of value, but record type supplied"))
    | DIV (e1, e2) ->
      (match (eval mem env e1) with
        | (Num n1, mem1) ->
          (match (eval mem1 env e2) with
            | (Num n2, mem2) -> (Num (n1/n2), mem2)
            | (Bool _, _) -> raise(Error "DIV : Expected int type of value, but bool type supplied")
            | (Unit, _) -> raise (Error "DIV : Expected int type of value, but unit type supplied")
            | (Record _,_) -> raise (Error "DIV : Expected int type of value, but record type supplied"))
        | (Bool _, _) -> raise(Error "DIV : Expected int type of value, but bool type supplied")
        | (Unit, _) -> raise (Error "DIV : Expected int type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "DIV : Expected int type of value, but record type supplied"))
    | EQUAL (e1, e2) ->
      (match (eval mem env e1) with
        | (Num n1, mem1) ->
          (match (eval mem1 env e2) with
            | (Num n2, mem2) -> if n1 = n2 then (Bool true, mem2)
                                else (Bool false, mem2)
            | (Bool _, _) -> raise(Error "EQUAL : Expected int type of value, but bool type supplied")
            | (Unit, _) -> raise (Error "EQUAL : Expected int type of value, but unit type supplied")
            | (Record _,_) -> raise (Error "EQUAL : Expected int type of value, but record type supplied"))
        | (Bool b1, mem1) ->
          (match (eval mem1 env e2) with
            | (Bool b2, mem2) -> if b1=b2 then (Bool true, mem2)
                                 else (Bool false, mem2) 
            | (Num  _, _) -> raise(Error "EQUAL : Expected bool type of value, but int type supplied")
            | (Unit, _) -> raise (Error "EQUAL : Expected bool type of value, but unit type supplied")
            | (Record _,_) -> raise (Error "EQUAL : Expected bool type of value, but record type supplied"))
        | (Unit, mem1) -> 
          (match (eval mem1 env e2) with
            | (Unit, mem2) -> (Bool true, mem2)
            | (Bool _, _) -> raise(Error "EQUAL : Expected unit type of value, but bool type supplied")
            | (Num  _, _) -> raise(Error "EQUAL : Expected unit type of value, but int type supplied")
            | (Record _,_) -> raise (Error "EQUAL : Expected unit type of value, but record type supplied"))
        | (Record _,_) -> raise (Error "EQUAL : Expected int/bool/unit type of value, but record type supplied"))
    | LESS (e1, e2) ->
       (match (eval mem env e1) with
        | (Num n1, mem1) ->
          (match (eval mem1 env e2) with
            | (Num n2, mem2) -> if n1 < n2 then (Bool true, mem2)
                                else (Bool false, mem2)
            | (Bool _, _) -> raise(Error "LESS : Expected int type of value, but bool type supplied")
            | (Unit, _) -> raise (Error "LESS : Expected int type of value, but unit type supplied")
            | (Record _,_) -> raise (Error "LESS : Expected int type of value, but record type supplied"))
        | (Bool _, _) -> raise(Error "LESS : Expected int type of value, but bool type supplied")
        | (Unit, _) -> raise (Error "LESS : Expected int type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "LESS : Expected int type of value, but record type supplied"))    
    | NOT e1 ->
      (match (eval mem env e1) with
      | (Bool b1, mem1) -> (Bool (not b1), mem1)
      | (Num _, _) -> raise(Error "NOT : Expected bool type of value, but int type supplied")
      | (Unit, _) -> raise (Error "NOT : Expected bool type of value, but unit type supplied")
      | (Record _,_) -> raise (Error "NOT : Expected bool type of value, but record type supplied"))
    | SEQ (e1,e2) ->
      (match (eval mem env e1) with
        | (v1,mem1) -> 
          (match (eval mem1 env e2) with
            | (v2, mem2) -> (v2, mem2)))
    | IF (e1,e2,e3) ->
      (match (eval mem env e1) with
        | (Bool b1, mem1) -> if b1 then (eval mem1 env e2)
                             else (eval mem1 env e3)
        | (Num _, _) -> raise(Error "IF : Expected bool type of value, but int type supplied")
        | (Unit, _) -> raise (Error "IF : Expected bool type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "IF : Expected bool type of value, but record type supplied"))    
    | WHILE (e1, e2) ->
      (match (eval mem env e1) with
        | (Bool true, mem1) -> 
          (match (eval mem1 env e2) with
            | (v1, mem2) -> (eval mem2 env e))
        | (Bool false, mem1) -> (Unit, mem1)            
        | (Num _, _) -> raise(Error "WHILE : Expected bool type of value, but int type supplied")
        | (Unit, _) -> raise (Error "WHILE : Expected bool type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "WHILE : Expected bool type of value, but record type supplied"))    
    | LETV (x,e1,e2) ->
      (match (eval mem env e1) with
       | (v1, mem1) -> 
          (match (Mem.alloc mem1) with
            | (loc, mem2) ->
              (match (Env.bind env x (Addr loc)) with
                | env1 -> eval (Mem.store mem2 (env_loc env1 x) v1) env1 e2)))        
    | LETF (f, xlist, e1, e2) -> 
      (match (Env.bind env f (Proc (xlist, e1, env))) with
        | env1 -> eval mem env1 e2)
    | CALLV (f, elist) -> 
        let rec evalList elist vlist mem1=
          (match elist with
            | ([]) -> (vlist, mem)
            | (hd::tl) -> 
              (match (eval mem env hd) with
                | (v1, mem1) -> evalList tl (vlist@[v1]) mem1))
        in (match (evalList elist [] mem) with
            | (vlist1, mem2) ->
              (match (env_proc env f) with
                | (xlist, e1, env) ->
                  let rec bindetox bvlist bxlist benv bmem =
                    (match bvlist with
                      | ([]) -> 
                        (match bxlist with
                          | ([]) -> eval bmem benv e1
                          | (xhd::xtl) -> raise (Error "Wrong Parameter"))
                      | (hd::tl) ->
                        (match bxlist with
                          | ([]) -> raise (Error "Wrong Parameter")
                          | (xhd::xtl) -> 
                            (match (Mem.alloc bmem) with 
                              | (loc, bmem1) -> 
                                (match Env.bind benv xhd (Addr loc) with
                                  | env1 -> 
                                    (match (Mem.store bmem1 loc hd) with
                                      | bmem2 -> bindetox tl xtl env1 bmem2)))))
                  in bindetox vlist1 xlist env mem2))
    | CALLR (f, xlist) -> raise (Error "fuck")
    | RECORD xexplist ->  raise (Error "fuck")
    | FIELD (e1, x) -> raise (Error "fuck")
    | ASSIGN (x, e1) -> 
      (match (eval mem env e1) with
        | (v1, mem1) ->  (v1, Mem.store mem1 (env_loc env x) v1 ))
(*)    | ASSIGNF (e1, x, e2) -> *)
    | READ x ->
      let n = read_int () in
      (Num n, Mem.store mem (env_loc env x) (Num n))
    | WRITE e1 ->
      (match (eval mem env e1) with
        | (Num n1, mem1) ->
          begin
            print_endline (string_of_int n1);
            (Num n1, mem1)
          end
        | (Bool _, _) -> raise (Error "WRITE : Expected int type of value, but bool type supplied")
        | (Unit, _) -> raise (Error "WRITE : Expected int type of value, but unit type supplied")
        | (Record _,_) -> raise (Error "WRITE : Expected int type of value, but record type supplied"))
    | _ -> raise (Error("not implemented")) (* implement it! *)

  let run (mem, env, pgm) = 
    let (v,_) = eval mem env pgm in
    v


end


(*fun x -> if x = id then loc else Not_bound
fun x -> if x = id2 then loc2 else if x = id then loc else Not_bound*)

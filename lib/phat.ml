open Core.Std
open Phat_core2
open Result.Monad_infix

(* Many functions not tail-recursive. Considered okay because paths
   are unlikely to be very long.
*)

(******************************************************************************)
(* Types                                                                      *)
(******************************************************************************)
type name = string with sexp

type abs
type rel

type dir
type file

type (_,_,_) cons =
  | RR : (rel,rel,rel) cons
  | RA : (rel,abs,abs) cons
  | AR : (abs,rel,abs) cons
  | AA : (abs,abs,abs) cons

type (_,_) impl =
  | R  : (rel,rel) impl
  | R' : (rel,abs) impl
  | A  : (abs,abs) impl

type ('kind,'res_kind,'obj) item =
| Root : (abs,abs,dir) item
| File : name -> (rel,rel,file) item
| Dir : name -> (rel,rel,dir) item
| Link : name * (_,'res_kind,'obj) path -> (rel,'res_kind,'obj) item
| Dot : (rel,rel,dir) item
| Dotdot : (rel,rel,dir) item

and ('kind,'res_kind,'obj) path =
| Item : ('kind,'res_kind,'obj) item * ('kind,'res_kind) impl -> ('kind,'res_kind,'obj) path
| Cons :
    ('k1,'k2,'k) cons *
    ('res_k1,'res_k2,'res_k) cons *
    ('k, 'res_k) impl *
    ('k1,'res_k1,dir) item * ('k2,'res_k2,'o) path -> ('k,'res_k,'o) path

type file_path = (abs,abs,file) path
type dir_path = (abs,abs,dir) path


(******************************************************************************)
(* Names                                                                      *)
(******************************************************************************)
let name s =
  if String.mem s '/' then
    error "slash not allowed in file or directory name" s sexp_of_string
  else if s = "." || s = ".." || s = "" then
    error "invalid file or directory name" s sexp_of_string
  else
    Ok s


(******************************************************************************)
(* Operators                                                                  *)
(******************************************************************************)

let rec concat : type a b c a' b' c' obj .
  (a,b,c) cons -> (a',b',c') cons -> (c,c') impl -> (a,a',dir) path -> (b,b',obj) path -> (c,c',obj) path
  = fun cons cons' impl x y ->
    match cons, cons', impl, x with
    | RR, RR, R, Item (i,R) -> Cons (cons,cons',R,i,y)
    | RR, RR, R, Cons (RR,RR,R,x1,x2) -> Cons (RR,RR,R,x1,concat RR RR R x y)
    | RR, RA, R', Cons (RR,RR,R,x1,x2) -> Cons (RR,RA,R',x1,concat RR RA R' x y)
    | RR, RA, R', Item (i,R) -> Cons (RR,RA,R',i,y)
    | RR, AR, R',  Item (i,R') -> Cons (RR,AR,R',i,y)
    | RR, AR, R', Cons (RR,AR,R',x1,x2) -> Cons (RR,AR,R',x1,concat RR RR R x2 y)
    | RR, AR, R', Cons (RR,RA,R',x1,x2) -> Cons (RR,RA,R',x1,concat RR AR R' x2 y)
    | RR, AR, R', Cons (RR,AA,R',x1,x2) -> Cons (RR,AA,R',x1,concat RR AR R' x2 y)
    | RR, AA, R', Item (i,R') -> Cons (RR, AA,R', i, y)
    | RR, AA, R', Cons (RR,AR,R',x1,x2) -> Cons (RR, AA,R',x1,concat RR RA R' x2 y)
    | RR, AA, R', Cons (RR,RA,R',x1,x2) -> Cons (RR, RA,R',x1,concat RR AA R' x2 y)
    | RR, AA, R', Cons (RR,AA,R',x1,x2) -> Cons (RR, AA,R',x1,concat RR AA R' x2 y)

let impl_of_cons : type b1 b2 b. (b1,b2,b) cons -> (b,b) impl = function
  | RR -> R
  | RA -> A
  | AR -> A
  | AA -> A

let rec resolve : type a b c. (a,b,c) path -> (b,b,c) path =
  let resolve_item : type a b c. (a,b,c) item -> (b,b,c) path = function
    | Root -> Item (Root,A)
    | File _ as i -> Item (i,R)
    | Dir _ as i -> Item (i,R)
    | Link (_, target) -> resolve target
    | Dot -> Item (Dot, R)
    | Dotdot -> Item (Dotdot, R)
  in
  function
  | Item (x,_) -> resolve_item x
  | Cons (cons, cons', impl, item, path) ->
    concat cons' cons' (impl_of_cons cons') (resolve_item item) (resolve path)

let rec parent : type a b obj. (a,b,obj) path -> (a,b,dir) path =
  function
  | Item (Root,_) as p -> p
  | Item (File _, _) -> Item (Dot, R)
  | Item (Dir _, _) -> Item (Dot, R)
  | Item (Link _,_) -> Item (Dot, R)
  | Item (Dot,_) -> Item (Dotdot, R)
  | Item (Dotdot,_) as p -> Cons (RR, RR, R, Dotdot, p)
  (* | Cons (cons, item, path) -> Cons(cons, item, parent path) *)

let rec normalize : type a b . (a,b) path -> (a,b) path =
  fun path -> match path with
    | Item Root -> path
    | Item (File _) -> path
    | Item (Dir _) -> path
    | Item Dot -> path
    | Item Dotdot -> path
    | Item (Link (_,path)) -> normalize path
    | Cons (cons, dir, path) ->
      let path = normalize path in
      match cons, dir, path with
      | _, _, Item (Link _) -> assert false
      | RA, _, (Item Root as p) -> p
      | AA, _, (Item Root as p) -> p
      | _, Root, Item (File _) -> Cons (cons, dir, path)
      | _, Root, Item (Dir _)  -> Cons (cons, dir, path)
      | _, Dir _, Item (File _) -> Cons(cons, dir, path)
      | _, Dir _, Item (Dir _) -> Cons (cons, dir, path)
      | RR, Dir _, Item Dot -> Item dir
      | RR, Dir _, Item Dotdot -> Item Dot
      | _, Dir _, Cons(_, Dir _, _) -> Cons (cons, dir, path)
      | RA, Dir _, Cons(_, Root, _) -> path
      | _, _, Cons (_, Link _, _) -> assert false
      | _, _, Cons (_, Dot, _) -> assert false
      | RR, Dir _, Cons (RR, Dotdot, path) -> path
      | RA, Dir _, Cons (RA, Dotdot, path) -> path
      | _, Link(_, dir), _ -> normalize (concat cons dir path)
      | RR, Dot, _ -> path
      | RA, Dot, _ -> path
      | _, Dotdot, Cons _ -> Cons (cons, dir, path)
      | _, Dotdot, Item (File _) -> Cons (cons, dir, path)
      | _, Dotdot, Item (Dir _) -> Cons (cons, dir, path)
      | RR, Dotdot, Item Dot -> Item Dotdot
      | _, Dotdot, Item Dotdot -> Cons (cons, dir, path)
      | AA, Root, Cons (_, Root, _) -> path
      | _, Root, Cons (_, Dir _, _) -> Cons (cons, dir, path)
      | AA, Root, Cons (RA, Dotdot, path) -> normalize (Cons (cons, Root, path))
      | AR, Root, Cons (RR, Dotdot, path) -> normalize (Cons (cons, Root, path))
      | AR, Root, Item Dot -> Item Root
      | AR, Root, Item Dotdot -> Item Root

let equal p q =
  let equal_item : type a b . (a,b) item -> (a,b) item -> bool =
    fun p q -> match p,q with
      | Root, Root -> true
      | Root, _ -> false
      | _, Root -> false
      | File p, File q -> String.equal p q
      | File _, _ -> false
      | _, File _ -> false
      | Dir p, Dir q -> String.equal p q
      | Dir _, _ -> false
      | _, Dir _ -> false
      | Link _, _ -> assert false
      | _, Link _ -> assert false
      | Dot, Dot -> true
      | Dot, _ -> false
      | _, Dot -> false
      | Dotdot, Dotdot -> true
  in
  let rec equal_normalized : type a b . (a,b) path -> (a,b) path -> bool =
    fun p q -> match p,q with
    | Item p, Item q -> equal_item p q
    | Cons(RR, p_dir,p_path), Cons(RR, q_dir,q_path) ->
      (equal_item p_dir q_dir) && (equal_normalized p_path q_path)
    | Cons(AR, p_dir,p_path), Cons(AR, q_dir,q_path) ->
      (equal_item p_dir q_dir) && (equal_normalized p_path q_path)
    | Cons(RA, p_dir,p_path), Cons(RA, q_dir,q_path) ->
      (equal_item p_dir q_dir) && (equal_normalized p_path q_path)
    | Cons(AA, p_dir,p_path), Cons(AA, q_dir,q_path) ->
      (equal_item p_dir q_dir) && (equal_normalized p_path q_path)
    | _, _ -> false
  in
  equal_normalized (normalize p) (normalize q)


(******************************************************************************)
(* Elems - internal use only                                             *)
(******************************************************************************)
module Elem : sig

  (** Like [item], an [elem] represents a single component of a path
      but is less strongly typed. It is a string guaranteed to be
      either a [name] or ".", "", "..", or "/". *)
  type elem = private string

  (** List guaranteed to be non-empty. *)
  type elems = private elem list

(*  val elem : string -> elem Or_error.t  # Avoid unused warning *)
  val elems : string -> elems Or_error.t

  val item_to_elem : (_,_) item -> elem

  val rel_dir_of_elems : elems -> (rel,dir) path Or_error.t
  val dir_of_elems : elems -> (abs,dir) path Or_error.t
  val rel_file_of_elems : elems -> (rel,file) path Or_error.t
  val file_of_elems : elems -> (abs,file) path Or_error.t

end = struct
  type elem = string with sexp
  type elems = elem list with sexp

  let elem s = match s with
    | "/" | "" | "." | ".." -> Ok s
    | _ -> name s

  let elems = function
    | "" -> Or_error.error_string "invalid empty path"
    | "/" -> Ok ["/"]
    | s ->
      let s,leading_slash = match String.chop_prefix s ~prefix:"/" with
        | None -> s,false
        | Some s -> s,true
      in
      Result.List.map ~f:elem (String.split s ~on:'/')
      >>| fun l ->
      if leading_slash then "/"::l else l

  let item_to_elem : type a b . (a,b) item -> elem = function
    | Root -> "/"
    | Dir x -> x
    | File x -> x
    | Link (x,_) -> x
    | Dot -> "."
    | Dotdot -> ".."

  let rel_dir_of_elems elems : (rel,dir) path Or_error.t =
    match elems with
    | [] -> assert false
    | "/"::_ ->
      error "relative path cannot begin with root directory"
        elems sexp_of_elems
    | _::tl ->
      if List.mem tl "/" then
        error "root directory can only occur as first item in path"
          elems sexp_of_elems
      else
        let item = function
          | "/" -> assert false
          | "" | "." -> Dot
          | ".." -> Dotdot
          | x -> (Dir x)
        in
        let rec loop = function
          | [] -> assert false
          | x::[] -> Item (item x)
          | x::elems -> Cons (RR, item x, loop elems)
        in
        Ok (loop elems)

  let dir_of_elems elems : (abs,dir) path Or_error.t =
    match elems with
    | [] -> assert false
    | "/"::[] -> Ok (Item Root)
    | "/"::tl -> (
      if List.mem tl "/" then
        error "root directory can only occur as first item in path"
          elems sexp_of_elems
      else (
        rel_dir_of_elems tl >>| fun reldir ->
        Cons (AR, Root, reldir)
      )
    )
    | _ ->
      error "absolute path must begin with root directory"
        elems sexp_of_elems

  let rel_file_of_elems elems : (rel,file) path Or_error.t =
    match elems with
    | [] -> assert false
    | "/"::_ ->
      error "relative path cannot begin with root directory"
        elems sexp_of_elems
    | _ -> (
      let elems_rev = List.rev elems in
      let last = List.hd_exn elems_rev in
      let elems = List.rev (List.tl_exn elems_rev) in
      match last with
      | "." | "" | ".." ->
        error "path cannot be treated as file" elems sexp_of_elems
      | _ ->
        match elems with
        | [] -> Ok (Item (File last))
        | _ ->
          rel_dir_of_elems elems >>| fun dir ->
          concat RR dir (Item (File last))
    )

  let file_of_elems elems : (abs,file) path Or_error.t =
    match elems with
    | [] -> assert false
    | "/"::[] ->
      error "root directory cannot be treated as file"
        elems sexp_of_elems
    | "/"::rest-> (
      let rest_rev = List.rev rest in
      let last = List.hd_exn rest_rev in
      let rest = List.rev (List.tl_exn rest_rev) in
      match last with
      | "." | "" | ".." ->
        error "path cannot be treated as file" elems sexp_of_elems
      | _ ->
        dir_of_elems ("/"::rest) >>| fun dir ->
        concat AR dir (Item (File last))
    )
    | _ ->
      error "absolute path must begin with root directory"
        elems sexp_of_elems

end
open Elem


(******************************************************************************)
(* Constructors                                                               *)
(******************************************************************************)
let root = Item Root
let rel_dir_path s = elems s >>= rel_dir_of_elems
let dir_path s = elems s >>= dir_of_elems
let rel_file_path s = elems s >>= rel_file_of_elems
let file_path s = elems s >>= file_of_elems


(******************************************************************************)
(* Deconstructors                                                             *)
(******************************************************************************)
let rec to_elem_list : type a b . (a,b) path -> elem list = function
  | Item x -> [item_to_elem x]
  | Cons (_, item, path) -> (item_to_elem item) :: (to_elem_list path)

let to_list path = (to_elem_list path :> string list)

let to_string t =
  to_list t |> function
  | "/"::path -> "/" ^ (String.concat ~sep:"/" path)
  | path -> String.concat ~sep:"/" path

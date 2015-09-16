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

type ('kind,'obj) item =
  | Root : (abs,dir) item
  | File : name -> (rel,file) item
  | Dir : name -> (rel,dir) item
  | Link : name * (_,'obj) path -> (rel,'obj) item
  | Dot : (rel,dir) item
  | Dotdot : (rel,dir) item

and ('kind,'obj) path =
  | Item : ('kind,'obj) item -> ('kind,'obj) path
  | Cons : ('a,dir) item * (_,'obj) path -> ('a,'obj) path

type 'a some_kind_of_path =
  | Abs_path of (abs,'a) path
  | Rel_path of (rel,'a) path

type file_path = (abs,file) path
type dir_path = (abs,dir) path


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

let rec concat
  : type a b kind . (a,dir) path -> (b,kind) path -> (a,kind) path
  = fun x y ->
    match x with
    | Item x -> Cons (x,y)
    | Cons (x1, x2) -> Cons (x1, concat x2 y)

let is_absolute
  : type a k. (a,k) path -> bool
  = function
    | Item Root -> true
    | Cons (Root, _) -> true
    | _ -> false

let rec resolve : type k o. (k,o) path -> o some_kind_of_path =
  function
  | Item x -> resolve_item x
  | Cons (item, path) ->
    match resolve_item item, resolve path, is_absolute path with
    | Rel_path x, Rel_path y, _ -> Rel_path (concat x y)
    | Rel_path x, Abs_path y, true -> Rel_path (concat x y)
    | Rel_path x, Abs_path y, false -> Abs_path y
    | Abs_path x, Rel_path y, _ -> Abs_path (concat x y)
    | Abs_path x, Abs_path y, true -> Abs_path (concat x y)
    | Abs_path x, Abs_path y, false -> Abs_path y

and resolve_item : type k o . (k,o) item -> o some_kind_of_path = fun x ->
  match x with
  | Root -> Abs_path (Item x)
  | File _ -> Rel_path (Item x)
  | Dir _ -> Rel_path (Item x)
  | Link (_, target) -> resolve target
  | Dot -> Rel_path (Item x)
  | Dotdot -> Rel_path (Item x)

let rec parent : type a b . (a,b) path -> (a,dir) path =
  fun path -> match path with
  | Item Root -> path
  | Item (File _) -> Item Dot
  | Item (Dir _) -> Item Dot
  | Item (Link _) -> Item Dot
  | Item Dot -> Item Dotdot
  | Item Dotdot -> Cons (Dotdot, path)
  | Cons (item, path) -> Cons (item, parent path)

let rec normalize : type a b . (a,b) path -> (a,b) path =
  fun path -> match path with
    | Item _ -> path
    | Cons (dir, path) ->
      let path = normalize path in
      match dir, path with
      | _, Item Dot -> Item dir
      | _, Item Root -> Item dir
      | Dot, Item (File _) -> path
      | Dot, Item (Dir _) -> path
      | Dot, Item (Link _) -> path
      | Dot, Item Dotdot -> path
      | Dot, Cons (Root, path') -> normalize (Cons (Dot, path'))
      | Dot, Cons (Dir _, _) -> path
      | Dot, Cons (Link _, _) -> path
      | Dot, Cons (Dotdot, _) -> path
      | _, Cons (Dot, _) -> assert false
      | Root, Cons (Dotdot, path') -> normalize (Cons (Root, path'))
      | _, _ -> Cons (dir, path)

let rec equal
  : type a b c d . (a,b) path -> (c,d) path -> bool
  = fun p q -> equal_normalized (normalize p) (normalize q)

and equal_normalized : type a b c d . (a,b) path -> (c,d) path -> bool =
  fun p q -> match p, q with
    | Item p, Item q -> equal_item p q
    | Cons(p_dir, p_path), Cons(q_dir, q_path) ->
      (equal_item p_dir q_dir) &&
      (
        match p_path, q_path with
        | Item Root, Item Root -> equal_normalized p_path q_path
        | Item Dot, Item Dot -> equal_normalized p_path q_path
        | Item Dotdot, Item Dotdot -> equal_normalized p_path q_path
        | Item (File _), Item (File _) -> equal_normalized p_path q_path
        | Item (Dir _), Item (Dir _) -> equal_normalized p_path q_path
        | Item (Link _), Item (Link _) -> equal_normalized p_path q_path
        | Cons (Root, _), Cons (Root, _) -> equal_normalized p_path q_path
        | Cons (Dot, _), Cons (Dot, _)  -> equal_normalized p_path q_path
        | Cons (Dotdot, _), Cons (Dotdot, _)  -> equal_normalized p_path q_path
        | Cons (Dir _, _), Cons (Dir _, _) -> equal_normalized p_path q_path
        | Cons (Link _, _), Cons (Link _, _) -> equal_normalized p_path q_path
        | _, _ -> false
      )
    | _, _ -> false

and equal_item : type a b c d. (a,b) item -> (c,d) item -> bool =
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
      | Link (np, p'), Link (nq, q') ->
        (String.equal np nq) && (equal p' q')
      | Link _, _ -> false
      | _, Link _ -> false
      | Dot, Dot -> true
      | Dot, _ -> false
      | _, Dot -> false
      | Dotdot, Dotdot -> true

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
          | x::elems -> Cons (item x, loop elems)
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
        Cons (Root, reldir)
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
          concat dir (Item (File last))
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
        concat dir (Item (File last))
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
  | Cons (item, path) -> (item_to_elem item) :: (to_elem_list path)

let to_list path = (to_elem_list path :> string list)

let to_string t =
  to_list t |> function
  | "/"::path -> "/" ^ (String.concat ~sep:"/" path)
  | path -> String.concat ~sep:"/" path

open! Core
open Types

type 'var t =
  { current_module : 'var module_
  ; seen_files : 'var module_ String.Table.t
  ; opened_modules : 'var module_ list
  ; locals : mono String.Map.t
  ; ty_vars : mono String.Map.t
  ; ty_var_counter : Counter.t
  ; var_counter : Counter.t
  ; seen_vars : String.Hash_set.t
  ; seen_types : String.Hash_set.t
  ; ty_var_map : mono String.Table.t option
  ; user_type_to_path : string list String.Table.t
  }

and 'var module_ =
  { name : string
  ; dir : string
  ; sub_modules : 'var module_ String.Table.t
  ; glob_vars : 'var String.Table.t
  ; types : user_type String.Table.t
  ; variant_to_type : user_type String.Table.t
  ; field_to_type : user_type String.Table.t
  ; mutable in_eval : bool
  ; parent : 'var module_ option
  }
[@@deriving sexp]

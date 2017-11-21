(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

open Util

open QcertCompiler.EnhancedCompiler
open QHLCQ

open Hlcq_j
  
let hlcquery_order_ASC s =
  hlcquery_order_ASC (Util.char_list_of_string s)

let hlcquery_order_DESC s =
  hlcquery_order_DESC (Util.char_list_of_string s)

let hlcquery_condition_expr_const d =
  hlcquery_condition_expr_const d

let hlcquery_condition_expr_param s =
  hlcquery_condition_expr_param (Util.char_list_of_string s)

let hlcquery_condition_expr_var s =
  hlcquery_condition_expr_var (Util.char_list_of_string s)

let hlcquery_condition_expr_unop u e =
  hlcquery_condition_expr_unop u e

let hlcquery_condition_expr_binop b e1 e2 =
  hlcquery_condition_expr_binop b e1 e2

let hlcquery_condition_and c1 c2 =
  hlcquery_condition_and c1 c2

let hlcquery_condition_or c1 c2 =
  hlcquery_condition_or c1 c2

let hlcquery_condition_contains c1 c2 =
  hlcquery_condition_contains c1 c2

let hlcquery_condition_lifted_expr e =
    hlcquery_condition_lifted_expr e

let hlcquery_statement b reg c o i1 i2 =
  hlcquery_statement b reg c o i1 i2

let hlcquery s1 s2 st =
  hlcquery (Util.char_list_of_string s1)
    (Util.char_list_of_string s2) st

(* Create AST from JSON structures *)
    
let hlcq_statement_of_select sel =
  hlcquery_statement
    (Util.char_list_of_string sel.hlcq_s_resource)
    None None None None None
  
let hlcq_of_hlcq_json q =
  hlcquery
    q.hlcq_q_identifier.hlcq_i_name
    q.hlcq_q_description
    (hlcq_statement_of_select q.hlcq_q_select)



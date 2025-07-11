(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Typing.Printer
module T = FStar.Tactics
open Pulse.Syntax.Printer
open Pulse.Typing

let print_st_typing #g #t #c (d:st_typing g t c)
  : T.Tac string 
  = "st typing is erased and cannot be printed"
  // match d with
  //   | T_Abs g x q b u body c tt body_typing ->
  //     Printf.sprintf "(T_Abs ... %s)" (print_st_typing body_typing)
    
  //   | T_STApp .. ->
  //     "T_STApp"

  //   | T_STGhostApp .. ->
  //     "T_STGhostApp"

  //   | T_Return .. ->
  //     "T_Return"

  //   | T_Lift _ _ _ _ d _ ->
  //     Printf.sprintf "(T_Lift %s)" (print_st_typing d)

  //   | T_Bind g e1 e2 c1 c2 b x c d1 _ d2 _ ->
  //     Printf.sprintf "(T_Bind %s %s)" (print_st_typing d1) (print_st_typing d2)

  //   | T_BindFn _ _ _ _ _ _ _ d1 _ _ d2 _ ->
  //     Printf.sprintf "(T_BindFn %s %s)" (print_st_typing d1) (print_st_typing d2)
    
  //   | T_If .. ->
  //     "T_If"

  //   | T_Match .. ->
  //     "T_Match"
    
  //   | T_Frame g e c frame _ body ->
  //     Printf.sprintf "(T_Frame %s %s)" (Pulse.Syntax.Printer.term_to_string frame) (print_st_typing body)

  //   | T_Equiv g e c c' d eq ->
  //     Printf.sprintf "(T_Equiv \n\t{%s}\n\t{%s}\n\t %s)"
  //        (Pulse.Syntax.Printer.comp_to_string c)
  //        (Pulse.Syntax.Printer.comp_to_string c')
  //        (print_st_typing d)
        
      
  //   | T_Sub _ _ _ _ d _ -> 
  //     Printf.sprintf "(T_Sub %s)" (print_st_typing d)

  //   | T_IntroPure .. ->
  //     "T_IntroPure"

  //   | T_ElimExists .. ->
  //     "T_ElimExists"

  //   | T_IntroExists .. ->
  //     "T_IntroExists"
    
  //   | T_While _ _ _ _ _ d1 d2 ->
  //     Printf.sprintf "(T_While %s %s)" (print_st_typing d1) (print_st_typing d2)

  //   | T_WithLocal _ _ _ _ _ _ _ _ _ _ d ->
  //     Printf.sprintf "(T_WithLocal %s)" (print_st_typing d)

  //   | T_WithLocalArray _ _ _ _ _ _ _ _ _ _ _ _ d ->
  //     Printf.sprintf "(T_WithLocalArray %s)" (print_st_typing d)  

  //   | T_Rewrite .. ->
  //     "T_Rewrite"
      
  //   | T_Admit .. ->
  //     "T_Admit"

  //   | T_Unreachable .. ->
  //     "T_Unreachable"

  //   | T_WithInv _ _ _ _ _ _ _ d _ ->
  //     Printf.sprintf "(T_WithInv %s)" (print_st_typing d)
    
  //   | T_Par _ _ _ _ _ _ _ _ d1 d2 ->
  //     Printf.sprintf "(T_Par %s %s)" (print_st_typing d1) (print_st_typing d2)
      
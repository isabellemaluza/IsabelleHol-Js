theory listateste
  imports Main
begin

(* Tipo para as operações *)
datatype oper = Soma | Sub | Mult | Div

(* Tipo para a expressão *)
datatype expr =
    Const int
  | Op oper expr expr

(* calcular o valor da expressão *)
fun calc :: "expr \<Rightarrow> int" where
  "calc (Const x) = x" |
  "calc (Op Soma e1 e2) = calc e1 + calc e2" |
  "calc (Op Sub  e1 e2) = calc e1 - calc e2" |
  "calc (Op Mult e1 e2) = calc e1 * calc e2" |
  "calc (Op Div  e1 e2) = calc e1 div calc e2"

definition exemplo4ops :: expr where
  "exemplo4ops =
     Op Soma
        (Op Sub
           (Const 5)
           (Op Mult (Const 7) (Const 2)))
        (Op Div
           (Const 8)
           (Const 4))"

value "calc exemplo4ops"  



(*
definition exemplo :: expr where
  "exemplo4ops =
     Op Mult
        (Op Sub
           (Const 9)
           (Op Soma (Const 12) (Const 5)))
        (Op Div
           (Const 8)
           (Const 4))

value "calc exemplo4ops"
 *)



(* (5 - 14) + (8 / 4) = -9 + 2 = -7 *)


(*op soma(const1) (const2) *)

end

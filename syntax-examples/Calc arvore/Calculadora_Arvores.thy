theory Calculadora_Arvores
  imports Main
begin
datatype oper = Soma | Sub | Mult | Div


datatype expr =
    Const int
  | Op oper expr expr

fun calc :: "expr => int" where
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

end
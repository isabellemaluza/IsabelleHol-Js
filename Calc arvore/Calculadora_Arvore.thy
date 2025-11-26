theory Calculadora_Arvore
  imports Main
begin

datatype expr =
    Num int
  | Soma expr expr
  | Subtracao expr expr
  | Multiplicacao expr expr
  | Divisao expr expr

fun avaliar :: "expr \<Rightarrow> int" where
  "avaliar (Num x) = x" |
  "avaliar (Soma e1 e2) = (avaliar e1) + (avaliar e2)" |
  "avaliar (Subtracao e1 e2) = (avaliar e1) - (avaliar e2)" |
  "avaliar (Multiplicacao e1 e2) = (avaliar e1) * (avaliar e2)" |
  "avaliar (Divisao e1 e2) = (if avaliar e2 \<noteq> 0 then (avaliar e1) div (avaliar e2) else 0)"


value "avaliar (Soma (Num 3) (Num 5))" 
value "avaliar (Multiplicacao (Soma (Num 2) (Num 3)) (Num 4))"
value "avaliar (Divisao (Num 10) (Num 2))"
value "avaliar (Subtracao (Num 7) (Multiplicacao (Num 2) (Num 3)))"

end

theory semana
  imports Main
begin

datatype dia = Segunda | Terca | Quarta | Quinta | Sexta | Sabado | Domingo

fun prox :: "dia \<Rightarrow> dia" where
  "prox Segunda = Terca" |
  "prox Terca = Quarta" |
  "prox Quarta = Quinta" |
  "prox Quinta = Sexta" |
  "prox Sexta = Sabado" |
  "prox Sabado = Domingo" |
  "prox Domingo = Segunda"

fun antes :: "dia \<Rightarrow> dia" where
  "antes Segunda = Domingo" |
  "antes Terca = Segunda" |
  "antes Quarta = Terca" |
  "antes Quinta = Quarta" |
  "antes Sexta = Quinta" |
  "antes Sabado = Sexta" |
  "antes Domingo = Sabado"

fun numero :: "dia \<Rightarrow> int" where
  
  "numero Segunda = 2" |
  "numero Terca = 3" |
  "numero Quarta = 4" |
  "numero Quinta = 5" |
  "numero Sexta = 6" |
  "numero Sabado = 7" |
  "numero Domingo = 1" 

fun nome :: "int \<Rightarrow> dia option" where
   "nome n = (if n = 1 then Some Domingo
         else if n = 2 then Some Segunda
         else if n = 3 then Some Terca
         else if n = 4 then Some Quarta
         else if n = 5 then Some Quinta
         else if n = 6 then Some Sexta
         else if n = 7 then Some Sabado
         else None)"


(*
procurar um maybe para o resto dos int
 *)



value "prox Terca"   
value "antes Quinta" 
value "numero Quarta" 
value "prox Sabado"
value "nome 2"
value "nome 14"

end
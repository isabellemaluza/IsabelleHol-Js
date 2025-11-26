theory Calculadora
  imports Main
begin

fun somar :: "int list \<Rightarrow> int" where
  "somar [] = 0" |
  "somar (x#xs) = x + somar xs"

fun multiplicar :: "int list \<Rightarrow> int" where
  "multiplicar [] = 1" |
  "multiplicar (x#xs) = x * multiplicar xs"

fun subtrair :: "int list \<Rightarrow> int" where
  "subtrair [] = 0" |
  "subtrair (x#[]) = x" |
  "subtrair (x#y#xs) = subtrair ((x - y)#xs)"

fun dividir :: "int list \<Rightarrow> int" where
  "dividir [] = 0" | 
  "dividir (x#[]) = x" |
  "dividir (x#y#xs) = dividir ((x div y)#xs)"

value "somar [1,2,3]" 
value "multiplicar [1,2,3]"
value "subtrair [10,2,5]"  
value "dividir [100,2,5]"
end

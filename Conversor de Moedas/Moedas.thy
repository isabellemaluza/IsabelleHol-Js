theory Moedas
  imports Complex_Main
begin

datatype moeda = Real | Dolar | Euro

fun taxa_em_reais :: "moeda \<Rightarrow> real" where
  "taxa_em_reais Real = 1" |
  "taxa_em_reais Dolar = 1 / 0.20" | 
  "taxa_em_reais Euro  = 1 / 0.18" 

fun converter :: "moeda \<Rightarrow> moeda \<Rightarrow> real \<Rightarrow> real" where
  "converter m1 m2 v = 
    (v * taxa_em_reais m1) / taxa_em_reais m2"

value "converter Real Dolar 10" 
value "converter Dolar Euro 5"   
value "converter Euro Real 20" 
value "converter Real Real 100"   

end




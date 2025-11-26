theory funcaorecursiva
  imports Main
begin

fun fatorial :: "nat \<Rightarrow> nat" where
  "fatorial 0 = 1" |
  "fatorial n = n * fatorial (n - 1)"


fun proximo :: "nat \<Rightarrow> nat" where
  "proximo n = n + 1"


fun infinito :: "nat \<Rightarrow> nat" where
  "infinito n = infinito n"


value "proximo 1"
value "fatorial 4"
value "infinito 1"
end
theory impar
  imports Main
begin

fun impares :: "nat list \<Rightarrow> nat list"
  where "impares [] = []" | 
        "impares (x # xs) =
 (if odd x then x # impares xs else impares xs)" 

value "impares [1, 2, 3, 4, 5, 6]"
value "impares (1#[2,3,4,5])"

end

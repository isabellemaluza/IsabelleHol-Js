theory Map
  imports Main
begin

fun distribuir :: "nat list \<Rightarrow> nat list" where
  "distribuir xs = map (\<lambda>x. x * 2) xs"

value "distribuir [1, 2, 3, 4]"

end

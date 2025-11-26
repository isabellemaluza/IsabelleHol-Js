theory conta
  imports Main
begin

fun conta :: "string \<Rightarrow> int" where
  "conta var = int (length var)"

value "conta ''Isa''"

end

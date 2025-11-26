theory arvores
  imports Main
begin

datatype 'a arvore = Vazia | No "'a arvore" 'a "'a arvore"


fun pre_ordem :: "'a arvore \<Rightarrow> 'a list" where
  "pre_ordem Vazia = []" |
  "pre_ordem (No esq x dir  ) = x # (pre_ordem esq @ pre_ordem dir)"


fun em_ordem :: "'a arvore \<Rightarrow> 'a list" where
  "em_ordem Vazia = []" |
  "em_ordem (No esq x dir) = em_ordem esq @ [x] @ em_ordem dir"


fun pos_ordem :: "'a arvore \<Rightarrow> 'a list" where
  "pos_ordem Vazia = []" |
  "pos_ordem (No esq x dir) = pos_ordem esq @ pos_ordem dir @ [x]"


value "let a = No (No Vazia (1::int) Vazia) 2 (No Vazia 3 Vazia) in pre_ordem a"
value "let a = No (No Vazia (1::int) Vazia) 2 (No Vazia 3 Vazia) in em_ordem a"
value "let a = No (No Vazia (1::int) Vazia) 2 (No Vazia 3 Vazia) in pos_ordem a"

end

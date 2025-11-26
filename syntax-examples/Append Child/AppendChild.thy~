theory AppendChild
  imports Main
begin

datatype node =  Element string "node list"| Text string                


definition doc :: node where
  "doc = Element ''bonjour'' [ Element ''oi'' [ Text ''hi'' ] ]"

fun appendChild :: "node \<Rightarrow> node \<Rightarrow> node" where
  "appendChild (Element tag children) child = Element tag (children @ [child])" |
  "appendChild (Text s) _ = Text s"


fun appendChild_by_tag :: "node \<Rightarrow> string \<Rightarrow> node \<Rightarrow> node" where
  "appendChild_by_tag (Element tag children) parent_tag child =
     (if tag = parent_tag
      then Element tag (children @ [child])
      else Element tag (map (\<lambda>n. appendChild_by_tag n parent_tag child) children))" |
  "appendChild_by_tag (Text s) _ _ = Text s"


value "appendChild (Element ''oi'' [Text ''Oi'']) (Element ''p'' [Text ''Paragrafo''])"
value "appendChild_by_tag doc ''oi'' (Element ''p'' [Text ''Paragrafo''])"

end

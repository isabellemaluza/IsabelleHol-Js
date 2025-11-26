theory ArvorePercursos
  imports Main
begin

(* ======== Definição da árvore binária ======== *)
datatype arvore =
    Vazia
  | No int arvore arvore

(* Inserir elemento na árvore binária de busca *)
fun inserir :: "int \<Rightarrow> arvore \<Rightarrow> arvore" where
  "inserir x Vazia = No x Vazia Vazia"
| "inserir x (No v esq dir) =
     (if x < v then No v (inserir x esq) dir
      else No v esq (inserir x dir))"

(* ======== Funções de percursos ======== *)

(* Pré-ordem: raiz \<rightarrow> esquerda \<rightarrow> direita *)
fun pre_ordem :: "arvore \<Rightarrow> int list" where
  "pre_ordem Vazia = []"
| "pre_ordem (No v esq dir) = [v] @ pre_ordem esq @ pre_ordem dir"

(* Em ordem: esquerda \<rightarrow> raiz \<rightarrow> direita *)
fun em_ordem :: "arvore \<Rightarrow> int list" where
  "em_ordem Vazia = []"
| "em_ordem (No v esq dir) = em_ordem esq @ [v] @ em_ordem dir"

(* Pós-ordem: esquerda \<rightarrow> direita \<rightarrow> raiz *)
fun pos_ordem :: "arvore \<Rightarrow> int list" where
  "pos_ordem Vazia = []"
| "pos_ordem (No v esq dir) = pos_ordem esq @ pos_ordem dir @ [v]"

(* Percurso por nível (BFS) *)
fun nivel_a_nivel_aux :: "arvore list \<Rightarrow> int list" where
  "nivel_a_nivel_aux [] = []"
| "nivel_a_nivel_aux (Vazia # resto) = nivel_a_nivel_aux resto"
| "nivel_a_nivel_aux ((No v e d) # resto) =
     v # nivel_a_nivel_aux (resto @ [e, d])"

fun nivel_a_nivel :: "arvore \<Rightarrow> int list" where
  "nivel_a_nivel t = nivel_a_nivel_aux [t]"

(* ======== LISTA DE NÚMEROS PARA MONTAR A ÁRVORE ======== *)
definition numeros :: "int list" where
  "numeros = [7, 3, 9, 1, 5, 8, 10]"
(* Altere os números acima como quiser *)

(* Construindo a árvore automaticamente a partir da lista *)
definition minha_arvore :: arvore where
  "minha_arvore = fold inserir numeros Vazia"

(* ======== RESULTADOS ======== *)
value "''Pre-ordem: '' @ show (pre_ordem minha_arvore)"
value "''Em ordem: '' @ show (em_ordem minha_arvore)"
value "''Pos-ordem: '' @ show (pos_ordem minha_arvore)"
value "''Nivel-a-nivel: '' @ show (nivel_a_nivel minha_arvore)"

end

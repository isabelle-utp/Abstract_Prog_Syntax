section \<open> Abstract Program Syntax \<close>

theory Abstract_Prog_Syntax
    imports "Shallow-Expressions.Shallow_Expressions"
begin

text \<open> In the world of UTP, many programming theories use the same basic program operators. This
  theory factors them all out as polymorphic constants and provides syntax translations to enable
  parsing and pretty printing. \<close>

consts
  ucond    :: "'p \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'p"
  useq     :: "'p \<Rightarrow> 'q \<Rightarrow> 'r" (infixr ";;" 55)
  uassigns :: "('a, 'b) psubst \<Rightarrow> 'p" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'p" ("II")
  utest    :: "('s \<Rightarrow> bool) \<Rightarrow> 'p"
  uwhile   :: "('s \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'p"

abbreviation (input) useqh :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" (infixr ";;\<^sub>h" 61) where
"useqh P Q \<equiv> (P ;; Q)"

expr_constructor ucond (0 2)
expr_constructor useq (0 1)
expr_constructor useqh (0 1)
expr_constructor uassigns
expr_constructor uskip
expr_constructor utest
expr_constructor uwhile

nonterminal elsebranch

syntax 
  "_ucond"         :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<lhd> _ \<rhd>/ _)" [52,0,53] 52)
  "_ucond_gen"     :: "logic \<Rightarrow> logic \<Rightarrow> elsebranch \<Rightarrow> logic" ("(2if _ /then /_/_ /fi)")
  "_ucond_elseif"  :: "logic \<Rightarrow> logic \<Rightarrow> elsebranch \<Rightarrow> elsebranch" ("( elseif _ /then /_/_)")
  "_ucond_else"    :: "logic \<Rightarrow> elsebranch" (" else /_")
  "_ucond_no_else" :: "elsebranch" ("")
  "_uassign"       :: "svid \<Rightarrow> logic \<Rightarrow> logic" (infix ":=" 61)
  "_swap"          :: "svid \<Rightarrow> svid \<Rightarrow> logic" ("swap'(_, _')") (* Atomic swap *)
  "_utest"         :: "logic \<Rightarrow> logic" ("\<questiondown>_?")
  "_uwhile"        :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("while _ do _ od")

translations
  "_ucond P b Q" => "CONST ucond P (b)\<^sub>e Q"
  "_ucond_gen b P Q" => "CONST ucond P (b)\<^sub>e Q"
  "_ucond_else P" => "P"
  "_ucond_no_else" => "II"
  "_ucond_gen b P (_ucond_else Q)" <= "CONST ucond P (b)\<^sub>e Q"
  "_ucond_elseif b P Q" => "CONST ucond P (b)\<^sub>e Q"
  "_ucond_elseif c Q (_ucond_else R)" <= "_ucond_else (CONST ucond Q (c)\<^sub>e R)"
  "_ucond_no_else" <= "_ucond_else II"
  "_ucond P b Q" == "CONST ucond P (b)\<^sub>e Q"
  "_uassign x e" == "CONST uassigns (CONST subst_upd (CONST subst_id) x (e)\<^sub>e)"
  "_uassign (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_uassign (x +\<^sub>L y) e" 
  "_swap x y" => "(x, y) := ($y, $x)"
  "_utest P" == "CONST utest (P)\<^sub>e"
  "_uwhile b P" == "CONST uwhile (b)\<^sub>e P"

end
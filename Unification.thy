chapter {* camr project *}

theory Unification imports Main begin

(* Assignment 1 *)

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

fun fv :: "('f, 'v) term \<Rightarrow> 'v set" where

type_synonym ('f, 'v) subst = "'v \<Rightarrow> ('f, 'v) term"

fun sapply :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixr "\<cdot>" 67) where 
  "sapply _ x = x" 

fun scomp :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" (infixl "\<circ>s" 75) where

lemma fv_sapply: "fv (\<sigma> \<cdot> t) = (\<Union>x \<in> fv t. fv (\<sigma> x))"
  sorry

lemma sapply_cong:
  assumes "\<And>x. x \<in> fv t \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "\<sigma> \<cdot> t = \<tau> \<cdot> t"
  sorry

lemma scomp_sapply: "(\<sigma> \<circ>s \<tau>) x = \<sigma> \<cdot> (\<tau> \<cdot> x)"
  sorry

lemma sapply_scomp_distr: "(\<sigma> \<circ>s \<tau>) \<cdot> t = \<sigma> \<cdot> (\<tau> \<cdot> t)"
  sorry

lemma scomp_assoc: "(\<sigma> \<circ>s \<tau>) \<circ>s \<rho> = \<sigma> \<circ>s (\<tau> \<circ>s \<rho>)"
  sorry

lemma scomp_var [simp]: "\<sigma> \<circ>s Var = \<sigma>"
  sorry

lemma var_scomp [simp]: "Var \<circ>s \<sigma> = \<sigma>"
  sorry







end

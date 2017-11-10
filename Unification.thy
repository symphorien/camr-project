chapter {* camr project *}

theory Unification imports Main begin

(* Assignment 1 *)

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

fun fv :: "('f, 'v) term \<Rightarrow> 'v set" where

type_synonym ('f, 'v) subst = "'v \<Rightarrow> ('f, 'v) term"

fun sapply :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixr "\<cdot>" 67) where 

fun scomp :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" (infixl "\<circ>s" 75) where

lemma fv_sapply: "fv (\<sigma> \<cdot> t) = (\<Union>x \<in> fv t. fv (\<sigma> x))"





end

chapter {* camr project *}

theory Unification imports Main begin

(* Assignment 1 *)

(****************************** definitions ******************************)

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

fun fv :: "('f, 'v) term \<Rightarrow> 'v set" where
  "fv (Var x) = {x}"
| "fv (Fun f xs) = (\<Union>x \<in> (set xs). fv x)"

print_theorems

type_synonym ('f, 'v) subst = "'v \<Rightarrow> ('f, 'v) term"

fun sapply :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixr "\<cdot>" 67) where 
  "sapply \<sigma> (Var x) = \<sigma> x"
| "sapply \<sigma> (Fun g xs) = Fun g (map (sapply \<sigma>) xs)"

print_theorems

fun scomp :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" (infixl "\<circ>s" 75) where
  "scomp \<sigma> \<tau> = (\<lambda>x. \<sigma> \<cdot> (\<tau> x))"



(******************************** lemmata **********************************) 

lemma fv_sapply: "fv (\<sigma> \<cdot> t) = (\<Union>x \<in> fv t. fv (\<sigma> x))"
  apply (induction t rule: fv.induct)
   apply (auto)
  done

lemma sapply_cong: "\<lbrakk>\<And>x. x \<in> fv t \<Longrightarrow> \<sigma> x = \<tau> x \<rbrakk> \<Longrightarrow> \<sigma> \<cdot> t = \<tau> \<cdot> t"
  apply (induction t rule: fv.induct)
   apply (auto)
  done

lemma scomp_sapply [simp]: "(\<sigma> \<circ>s \<tau>) x = \<sigma> \<cdot> (\<tau> x)"
  by simp

lemma sapply_scomp_distr [simp]: "(\<sigma> \<circ>s \<tau>) \<cdot> t = \<sigma> \<cdot> (\<tau> \<cdot> t)"
  apply simp
  apply (induction t rule: fv.induct)
   apply auto
  done

lemma scomp_assoc: "(\<sigma> \<circ>s \<tau>) \<circ>s \<rho> = \<sigma> \<circ>s (\<tau> \<circ>s \<rho>)"
proof -
  have "(\<sigma> \<circ>s \<tau>) \<circ>s \<rho> = (\<lambda>x. (\<sigma> \<circ>s \<tau>) \<cdot> \<rho> x)" by simp
  also have "... = (\<lambda>x. \<sigma> \<cdot> \<tau> \<cdot> \<rho> x)" by (simp only: sapply_scomp_distr)
  also have "... = \<sigma> \<circ>s (\<tau> \<circ>s \<rho>)" by simp
  finally show ?thesis .
qed

lemma scomp_var [simp]: "\<sigma> \<circ>s Var = \<sigma>"
  by simp

lemma var_sapply [simp]: "Var \<cdot> t = t"
  apply (induction t rule: fv.induct)
  by (auto simp add: map_idI)

lemma var_scomp [simp]: "Var \<circ>s \<sigma> = \<sigma>"
  by simp


(********************************** definitions ****************************)

definition sdom :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "sdom \<sigma> = {x | x. \<sigma> x \<noteq> Var x}"

definition sran :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set" where
  "sran \<sigma> = {\<sigma> x | x. x \<in> sdom \<sigma>}"

definition svran :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "svran \<sigma> = (\<Union> t \<in> sran \<sigma>. fv t)"

lemma sdom_elim [elim]: "\<sigma> x \<noteq> Var x \<Longrightarrow> x \<in> sdom \<sigma>"
  by (simp add: sdom_def)

lemma sdom_intro [intro]: "x \<in> sdom \<sigma> \<Longrightarrow> \<sigma> x \<noteq> Var x"
  by (simp add: sdom_def) 

lemma svran_elim [elim]: "\<lbrakk> x \<in> sdom \<sigma>; y \<in> fv (\<sigma> x) \<rbrakk> \<Longrightarrow> y \<in> svran \<sigma>"
  by (auto simp add: sdom_def sran_def svran_def)

lemma svran_intro [intro]: "y \<in> svran \<sigma> \<Longrightarrow> (\<exists>x \<in> sdom \<sigma>. y \<in> fv (\<sigma> x))"
  by (auto simp add: sdom_def sran_def svran_def)


(************************************ lemmata ******************************)

lemma sdom_var [simp]: "sdom Var = {}"
  by (simp add: sdom_def)

lemma svran_var [simp]: "svran Var = {}"
  by (simp add: svran_def sran_def)

lemma sdom_single_non_trivial [simp]: "t \<noteq> Var x \<Longrightarrow> sdom (Var (x := t)) = {x}"
  by (simp add: sdom_def)

lemma svran_single_non_trivial [simp]: "t \<noteq> Var x \<Longrightarrow> svran (Var (x := t)) = fv t"
  by (simp add: svran_def sran_def)

(*lemma "\<sigma> \<cdot> t = (fv t - sdom \<sigma>) \<union> ran \<sigma>"*)

(*lemma img_subst: "\<forall>x. \<sigma> x = Var y \<Longrightarrow> y \<in> (UNIV - sdom \<sigma>) \<union> svran \<sigma>"*)

lemma fv_sapply_sdom_svran: "x \<in> fv (\<sigma> \<cdot> t) \<Longrightarrow> x \<in> (fv t - sdom \<sigma>) \<union> svran \<sigma>"
  apply (simp add: fv_sapply)
  apply (auto)

lemma sdom_scomp: "sdom (\<sigma> \<circ>s \<tau>) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  by (auto simp add: sdom_def)

lemma svran_scomp: "svran (\<sigma> \<circ>s \<tau>) \<subseteq> svran \<sigma> \<union> svran \<tau>"
  apply (auto simp add: svran_intro)
  apply (rule svran_elim)
  apply (auto)
  apply (simp add: svran_intro)


(**************************************** definitions *********************************)

type_synonym ('f, 'v) equation = "('f, 'v) term \<times> ('f, 'v) term"

type_synonym ('f, 'v) equations = "('f, 'v) equation list"

fun fv_eq :: "('f, 'v) equation \<Rightarrow> 'v set" where
  "fv_eq (a, b) = fv a \<union> fv b"

fun fv_eqs :: "('f, 'v) equations \<Rightarrow> 'v set" where
  "fv_eqs l = (\<Union>x \<in> set l. fv_eq x)"

fun sapply_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" where
  "sapply_eq \<sigma> (a,b) = (sapply \<sigma> a, sapply \<sigma> b)"

print_theorems

fun sapply_eqs :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> ('f, 'v) equations" where
  "sapply_eqs \<sigma> l = map (sapply_eq \<sigma>) l"


(******************************** lemmata *************************************)

lemma fv_sapply_eq: "fv_eq (sapply_eq \<sigma> (a,b)) = fv (\<sigma> \<cdot> a) \<union> fv (\<sigma> \<cdot> b)"
  by auto

lemma fv_sapply_eqs: "fv_eqs (sapply_eqs \<sigma> l) = (\<Union>x \<in> set l. fv_eq (sapply_eq \<sigma> x))"
  by auto

lemma sapply_scomp_distrib_eq: "sapply_eq (\<sigma> \<circ>s \<tau>) (a,b) = (\<sigma> \<cdot> (\<tau> \<cdot> a), \<sigma> \<cdot> (\<tau> \<cdot> b))"
  apply (simp)
  apply (rule conjI)
  apply (induction a rule: fv.induct)
    apply auto
  apply (induction b rule: fv.induct)
   apply auto
  done

lemma sapply_scomp_distrib_eqs: "sapply_eqs (\<sigma> \<circ>s \<tau>) l = map (\<lambda>x. sapply_eq (\<sigma> \<circ>s \<tau>) x) l"
  apply (induction l)
  by auto


(******************************* definitions ************************************)

inductive unifies :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "\<lbrakk> \<sigma> \<cdot> a = \<sigma> \<cdot> b \<rbrakk> \<Longrightarrow> unifies \<sigma> (a, b)"

definition unifiess :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "unifiess \<sigma> l =  (\<forall> x \<in> set l. unifies \<sigma> x)"

print_theorems

fun is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "is_mgu \<sigma> l \<longleftrightarrow> (unifiess \<sigma> l \<and> (\<forall> \<tau>. unifiess \<tau> l \<longrightarrow> (\<exists> \<rho>. \<tau> = \<rho> \<circ>s \<sigma>)))"

fun measure2 :: "('f, 'v) equations \<Rightarrow> nat" where
  "measure2 (x # xs) = size x + measure2 xs"
| "measure2 [] = 0"

fun scomp_opt :: "('f, 'v) subst option \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst option" where
  "scomp_opt (Some \<sigma>) \<tau> = Some (\<sigma> \<circ>s \<tau>)"
| "scomp_opt None _ = None"

function (sequential) unify :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst option" where
  "unify [] = Some Var"
| "unify ((Var x, Var y) # xs) = (if x = y then unify xs else scomp_opt (unify (sapply_eqs (Var (x := Var y)) xs)) (Var (x := Var y)))"
| "unify ((Var x, b) # xs) = (if x \<in> fv b then None else scomp_opt (unify (sapply_eqs (Var (x := b)) xs)) (Var (x := b)))"
| "unify ((b, Var x) # xs) = unify ((Var x, b) # xs)"
| "unify ((Fun f l1, Fun g l2) # xs) = (if g = f then (if length l2 = length l1 then unify (xs @ (zip l1 l2)) else None) else None)"
by pat_completeness auto
termination 
  by (relation "measures [
  (\<lambda>U. card (fv_eqs U)), 
  (\<lambda>U. measure2 U), 
  (\<lambda>U. length U)]")
  (auto intro: card_insert_le card_mono psubset_card_mono split: if_split_asm)

print_theorems


(******************************** lemmata *********************************)


lemma lambda_simp:  "\<sigma> \<cdot> \<tau> \<cdot> a = (\<lambda>x. \<sigma> \<cdot> \<tau> x) \<cdot> a"
  apply (induction a rule: fv.induct)
  by auto

lemma unifies_sapply_eq [simp]: "unifies \<sigma> (sapply_eq \<tau> eq) \<longleftrightarrow> unifies (\<sigma> \<circ>s \<tau>) eq"
  apply (rule iffI)
  apply (cases eq)
  by (auto simp add: unifies.simps lambda_simp)

lemma unify_return: "unify l = Some \<sigma> \<Longrightarrow> unifiess \<sigma> l"
proof (induction l rule: unify.induct)
  case 1
  then show ?case by (simp add: unifiess.simps)
next
  case (2 x y xs)
then show ?case sorry
next
  case (3 x v va xs)
then show ?case sorry
next
  case (4 v va x xs)
then show ?case sorry
next
  case (5 f l1 g l2 xs)
then show ?case sorry
qed


lemma unify_mgu: "\<lbrakk>unify l = some \<sigma>; unifiess \<tau> l\<rbrakk> \<Longrightarrow> \<exists> \<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
  sorry

lemma unify_sound: "unify l = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> l"
  sorry

lemma unify_complete: "\<exists> \<sigma>. unifiess \<sigma> l \<Longrightarrow> (unify l = Some \<tau> \<and> unifiess \<tau> l)"
  sorry


lemma 3:
  fixes \<sigma> :: "('f, 'v) subst" 
    and l :: "('f, 'v) equations"
  assumes 1: "unify l = Some \<sigma>"
  shows subst_subs: "fv_eqs (sapply_eqs \<sigma> l) \<subseteq> fv_eqs l"
    and sdom_fv: "sdom \<sigma> \<subseteq> fv_eqs l"
    and svran_fv: "svran \<sigma> \<subseteq> fv_eqs l"
    and sdom_svran_disj: "sdom \<sigma> \<inter> svran \<sigma> = {}"
  sorry
  


lemma fv_subst: "unify l = Some \<sigma> \<Longrightarrow> fv_eqs (sapply_eqs \<sigma> l) \<subseteq> fv_eqs l"
  sorry

lemma fv_sdom: "unify l = Some \<sigma> \<Longrightarrow> sdom \<sigma> \<subseteq> fv_eqs l"
  sorry

lemma fv_svran: "unify l = Some \<sigma> \<Longrightarrow> svran \<sigma> \<subseteq> fv_eqs l"
  sorry

lemma sig_func: "unify l = Some \<sigma> \<Longrightarrow> sdom \<sigma> \<inter> svran \<sigma> = {}"
  sorry


(*********************************** definitions ***************************)

inductive wf_term :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  for arity :: "'f \<Rightarrow> nat"
  where
  "wf_term arity (Var _)"
| "(length l = arity f) \<Longrightarrow> \<forall> x \<in> set l. wf_term arity x \<Longrightarrow> wf_term arity (Fun f l)"

inductive wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool" where
  "\<lbrakk> \<forall>x. wf_term arity x \<longrightarrow> wf_term arity (\<sigma> \<cdot> x) \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"

print_theorems

inductive wf_eq :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "\<lbrakk> wf_term arity a; wf_term arity b \<rbrakk> \<Longrightarrow> wf_eq arity (a,b)"

inductive wf_eqs :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "\<lbrakk> \<forall>x \<in> set l. wf_eq arity x \<rbrakk> \<Longrightarrow> wf_eqs arity l" 


(********************************** lemmata **********************************)

lemma eq_comm: "Var y = x \<Longrightarrow> wf_term arity x"
  by (auto simp add: wf_term.intros)

lemma eq_comm1: "x = y \<Longrightarrow> wf_term arity x \<longleftrightarrow> wf_term arity y"
  by auto

lemma wf_term_sapply: "\<lbrakk> wf_term arity t; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> \<cdot> t)"
proof (induction "\<sigma> \<cdot> t")
  case (Var x)
  have "\<sigma> \<cdot> t = Var x" using \<open>Var x = \<sigma> \<cdot> t\<close> by simp 
  then show ?case by (simp add: wf_term.intros)
next
  case (Fun x1a x2)
  then show ?case using wf_subst.cases by auto
qed

lemma wf_subst_scomp: "\<lbrakk> wf_subst arity \<sigma>; wf_subst arity \<tau> \<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>s \<tau>)"
  by (metis sapply_scomp_distr wf_subst.intros wf_term_sapply)

lemma wf_subst_unify: "\<lbrakk> unify l = Some \<sigma>; wf_eqs arity l \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
  apply (induction l)
  sorry


end

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

definition scomp :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" (infixl "\<circ>s" 75) where
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
  by (simp add: scomp_def)

lemma sapply_scomp_distr [simp]: "(\<sigma> \<circ>s \<tau>) \<cdot> t = \<sigma> \<cdot> (\<tau> \<cdot> t)"
  apply (simp add: scomp_def)
  apply (induction t rule: fv.induct)
   apply auto
  done

lemma scomp_assoc: "(\<sigma> \<circ>s \<tau>) \<circ>s \<rho> = \<sigma> \<circ>s (\<tau> \<circ>s \<rho>)"
proof -
  have "(\<sigma> \<circ>s \<tau>) \<circ>s \<rho> = (\<lambda>x. (\<sigma> \<circ>s \<tau>) \<cdot> \<rho> x)" by (simp add: scomp_def)
  also have "... = (\<lambda>x. \<sigma> \<cdot> \<tau> \<cdot> \<rho> x)" by (simp only: sapply_scomp_distr)
  also have "... = \<sigma> \<circ>s (\<tau> \<circ>s \<rho>)" by (simp add: scomp_def)
  finally show ?thesis .
qed

lemma scomp_var [simp]: "\<sigma> \<circ>s Var = \<sigma>"
  by (simp add: scomp_def)

lemma var_sapply [simp]: "Var \<cdot> t = t"
  apply (induction t rule: fv.induct)
  by (auto simp add: map_idI)

lemma var_scomp [simp]: "Var \<circ>s \<sigma> = \<sigma>"
  by (simp add: scomp_def)


(********************************** definitions ****************************)

definition sdom :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "sdom \<sigma> = {x | x. \<sigma> x \<noteq> Var x}"

definition sran :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set" where
  "sran \<sigma> = {\<sigma> x | x. x \<in> sdom \<sigma>}"

definition svran :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "svran \<sigma> = (\<Union> t \<in> sran \<sigma>. fv t)"

lemma sdom_intro [intro]: "\<sigma> x \<noteq> Var x \<Longrightarrow> x \<in> sdom \<sigma>"
  by (simp add: sdom_def)

lemma sdom_dest [dest]: "x \<in> sdom \<sigma> \<Longrightarrow> \<sigma> x \<noteq> Var x"
  by (simp add: sdom_def) 

lemma svran_intro [intro]: "\<lbrakk> x \<in> sdom \<sigma>; y \<in> fv (\<sigma> x) \<rbrakk> \<Longrightarrow> y \<in> svran \<sigma>"
  by (auto simp add: sdom_def sran_def svran_def)

lemma svran_elim [elim]: "y \<in> svran \<sigma> \<Longrightarrow> (\<And>x. x \<in> sdom \<sigma> \<Longrightarrow> y \<in> fv (\<sigma> x) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp add: sdom_def sran_def svran_def)

lemma svran_dest [dest]: "y \<in> svran \<sigma> \<Longrightarrow> (\<exists>x \<in> sdom \<sigma>. y \<in> fv (\<sigma> x))"
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
proof (induction t)
  case (Var y)
  then have "x \<in> (\<Union>x \<in> fv (Var y). fv (\<sigma> x))" by (simp add: fv_sapply)
  then have "x \<in> fv (\<sigma> y)" by simp
  then show ?case 
proof (cases "\<sigma> y = Var y")
  case True
  then have "x \<in> {y}" using \<open>x \<in> fv (\<sigma> y)\<close> by simp
  then have 1: "x = y" by simp
  have 2: "y \<in> fv (Var y)" by simp
  have 3: "y \<notin> sdom \<sigma>" using \<open>\<sigma> y = Var y\<close> by (simp add: sdom_def)
  from 1 2 3 have "x \<in> fv (Var y) - sdom \<sigma>" by simp
  then show ?thesis by auto
next
  case False
  then have "y \<in> sdom \<sigma>" by (simp add: sdom_def)
  then have "x \<in> svran \<sigma>" using \<open>x \<in> fv (\<sigma> y)\<close> by auto
  then show ?thesis by simp
qed
next
  case (Fun x1a x2)
  then show ?case by auto
qed

lemma sdom_scomp: "sdom (\<sigma> \<circ>s \<tau>) \<subseteq> sdom \<sigma> \<union> sdom \<tau>"
  by (auto simp add: sdom_def)

lemma svran_scomp: "svran (\<sigma> \<circ>s \<tau>) \<subseteq> svran \<sigma> \<union> svran \<tau>"
proof (rule subsetI)
  fix x
  assume "x \<in> svran (\<sigma> \<circ>s \<tau>)"
  then obtain y where 0: "y \<in> sdom (\<sigma> \<circ>s \<tau>)" "x \<in> fv ((\<sigma> \<circ>s \<tau>) y)" by auto
  then have "x \<in> fv (\<sigma> \<cdot> (\<tau> y))" by (simp only: scomp_def)
  then have 1: "x \<in> (fv (\<tau> y) - sdom \<sigma>) \<or> x \<in> svran \<sigma>" by (blast dest: fv_sapply_sdom_svran)
  show "x \<in> svran \<sigma> \<union> svran \<tau>"
  proof(subst Un_commute, rule UnCI)
    assume "x \<notin> svran \<sigma>"
    then have "x \<in> (fv (\<tau> y) - sdom \<sigma>)" using 1 by simp
    then have 2: "x \<in> fv (\<tau> y)" by simp
    then show "x \<in> svran \<tau>"
    proof (cases "y \<in> sdom \<tau>")
      case True
      then have "x \<in> svran \<tau>" using \<open>x \<in> fv (\<tau> y)\<close> by (auto)
      then show ?thesis by simp
    next
      case False
      then have "\<tau> y = Var y" by (simp add: sdom_def)
      then have "x = y" using 2 by auto
      then have False  using \<open>x \<in> (fv (\<tau> y) - sdom \<sigma>)\<close> using \<open>x = y\<close> \<open>y \<notin> sdom \<tau>\<close> sdom_scomp[of \<sigma> \<tau>] 0 by auto
      then show ?thesis by simp
    qed
  qed
qed

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
  by (simp)

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
  apply (relation "measures [
  (\<lambda>U. card (fv_eqs U)), 
  (\<lambda>U. measure2 U), 
  (\<lambda>U. length U)]")
  apply (auto intro: card_insert_le card_mono psubset_card_mono split: if_split_asm)

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
  wf_term_intro_var:"wf_term arity (Var _)"
| wf_term_intro_fun:"(length l = arity f) \<Longrightarrow> \<forall> x \<in> set l. wf_term arity x \<Longrightarrow> wf_term arity (Fun f l)"

inductive wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool"
  for arity :: "'f \<Rightarrow> nat" where
  "\<lbrakk> \<forall>x. wf_term arity (\<sigma> x) \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"

inductive wf_eq :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "\<lbrakk> wf_term arity a; wf_term arity b \<rbrakk> \<Longrightarrow> wf_eq arity (a,b)"

lemma wf_eqE: "wf_eq arity (a, b) \<Longrightarrow> (wf_term arity a \<Longrightarrow> wf_term arity b \<Longrightarrow> P) \<Longrightarrow> P"
  using wf_eq.cases by auto

inductive wf_eqs :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "\<lbrakk> \<forall>x \<in> set l. wf_eq arity x \<rbrakk> \<Longrightarrow> wf_eqs arity l" 


(********************************** lemmata **********************************)

lemma eq_comm: "Var y = x \<Longrightarrow> wf_term arity x"
  by (auto simp add: wf_term.intros)

lemma eq_comm1: "x = y \<Longrightarrow> wf_term arity x \<longleftrightarrow> wf_term arity y"
  by auto

lemma wf_term_sapply: "\<lbrakk> wf_term arity t; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_term arity (\<sigma> \<cdot> t)"
proof (induction t)
  case (Var x)
  then show ?case
    by(auto simp add:wf_subst.simps intro: wf_term.intros)
next
  case (Fun s ts)
  let ?t = "Fun s ts"
  have x:"\<sigma> \<cdot> ?t = Fun s (map (sapply \<sigma>) ts)" (is "_ = Fun _ ?elts") by(simp)
  have "wf_term arity (Fun s ?elts)"
  proof(rule wf_term_intro_fun)
    have "length (map (op \<cdot> \<sigma>) ts) = length ts" by simp
    also have "... = arity s" 
      using `wf_term arity ?t`
      by(cases rule:wf_term.cases)
    finally show "length (map (op \<cdot> \<sigma>) ts) = arity s ".
  next
    have "\<And>x. x\<in>set (map (op \<cdot> \<sigma>) ts) \<Longrightarrow> wf_term arity x "
    proof -
      fix x
      assume "x\<in>set (map (op \<cdot> \<sigma>) ts)"
      then obtain z where "z\<in>set ts" and "x = \<sigma> \<cdot> z" by auto
      have "wf_term arity z"
        using `wf_term arity ?t`
        by(cases rule:wf_term.cases)(auto simp add:`z\<in>set ts`)
      from `z\<in> set ts` and `wf_term arity z` and `wf_subst arity \<sigma>` have "wf_term arity (\<sigma> \<cdot> z)" by(rule Fun.IH)
      then show "wf_term arity x" by(simp add:`x = \<sigma>\<cdot>z`)
    qed
    then show "\<forall>x\<in>set (map (op \<cdot> \<sigma>) ts). wf_term arity x" by blast
  qed
  then show "wf_term arity (\<sigma> \<cdot> ?t)" by(simp add:x)
qed

lemma wf_eq_sapply_eq: "\<lbrakk> wf_eq arity eq; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_eq arity (sapply_eq \<sigma> eq)"
  by(cases eq; auto simp add:wf_term_sapply elim!:wf_eqE intro!:wf_eq.intros)

lemma wf_subst_scomp: "\<lbrakk> wf_subst arity \<sigma>; wf_subst arity \<tau> \<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>s \<tau>)"
  by (simp add: wf_subst.simps wf_term_sapply)

lemma wf_subst_unify: "\<lbrakk> unify l = Some \<sigma>; wf_eqs arity l \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
  apply (induction l)
  sorry
end

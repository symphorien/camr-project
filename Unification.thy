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

print_theorems

definition unifiess :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "unifiess \<sigma> l =  (\<forall> x \<in> set l. unifies \<sigma> x)"

lemma unifiess_empty: "unifiess \<sigma> []"
  by (auto simp add: unifiess_def)

lemma unifiess_list: "\<lbrakk> unifies \<sigma> x; unifiess \<sigma> xs \<rbrakk> \<Longrightarrow> unifiess \<sigma> (x # xs)"
  by (auto simp add: unifies.intros unifiess_def)

lemma helper: "\<lbrakk> length l1 = length l2; (\<And>a b. (a,b) \<in> set (zip l1 l2) \<Longrightarrow> unifies \<sigma> (a,b)) \<rbrakk> \<Longrightarrow> unifiess \<sigma> (zip l1 l2)"
  apply (induction "zip l1 l2")
  by (auto simp add: unifiess_def)

lemma "\<lbrakk> \<forall>(a,b) \<in> set (zip l1 l2). f a = f b; length l1 = length l2 \<rbrakk> \<Longrightarrow> map f l1 = map f l2"
proof (induction "zip l1 l2")
  case Nil
  assume "\<forall>(a, b)\<in>set (zip l1 l2). f a = f b" 
     and "length l1 = length l2"
  have "length (zip l1 l2) = 0" using \<open>[] = zip l1 l2\<close> by simp
  then have "length l1 = 0" "length l2 = 0" using \<open>length l1 = length l2\<close> by (auto) 
  then have "l1 = []" "l2 = []" by auto
  then show ?case by simp
next
  case (Cons a xs)
  then have "zip l1 l2 = a # xs" by simp
  then have "hd (zip l1 l2) = a" by (simp add: hd_def)
  have "xs = tl (zip l1 l2)" using \<open>zip l1 l2 = a # xs\<close> by simp
  then show ?case oops


lemma "\<lbrakk> length l1 = length l2 \<rbrakk> \<Longrightarrow> unifiess \<sigma> (zip l1 l2) \<longleftrightarrow> unifies \<sigma> (Fun f l1, Fun f l2)"
proof (rule iffI)
  assume "length l1 = length l2"
     and "unifiess \<sigma> (zip l1 l2)"
  then have "\<forall>(a,b) \<in> set (zip l1 l2). \<sigma> \<cdot> a = \<sigma> \<cdot> b" by (auto simp add: unifiess_def unifies.simps)
  (*then have "\<forall>(a,b) \<in> set (zip (map (sapply \<sigma>) l1) (map (sapply \<sigma>) l2)). a = b"*) 
  then have "map (sapply \<sigma>) l1 = map (sapply \<sigma>) l2" using \<open>length l1 = length l2\<close> list_eq_iff_zip_eq[of "map (sapply \<sigma>) l1" "map (sapply \<sigma>) l2"] sorry
  then show  "unifies \<sigma> (Fun f l1, Fun f l2)" oops
next
  show "unifiess \<sigma> (zip l1 l2)" oops

fun is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "is_mgu \<sigma> l \<longleftrightarrow> (unifiess \<sigma> l \<and> (\<forall> \<tau>. unifiess \<tau> l \<longrightarrow> (\<exists> \<rho>. \<tau> = \<rho> \<circ>s \<sigma>)))"

fun measure2 :: "('f, 'v) equations \<Rightarrow> nat" where
  "measure2 (x # xs) = size x + measure2 xs"
| "measure2 [] = 0"

fun scomp_opt :: "('f, 'v) subst option \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst option" where
  "scomp_opt (Some \<sigma>) \<tau> = Some (\<sigma> \<circ>s \<tau>)"
| "scomp_opt None _ = None"

print_theorems

lemma scomp_some: "scomp_opt a b = Some c \<Longrightarrow> \<exists>\<sigma>. a = Some \<sigma>"
  apply (cases a)
  by auto

function (sequential) unify :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst option" where
  "unify [] = Some Var"
| "unify ((Var x, b) # xs) = (if b = Var x then unify xs else (if x \<in> fv b then None else scomp_opt (unify (sapply_eqs (Var (x := b)) xs)) (Var (x := b))))"
| "unify ((b, Var x) # xs) = unify ((Var x, b) # xs)"
| "unify ((Fun f l1, Fun g l2) # xs) = (if g = f then (if length l2 = length l1 then unify (xs @ (zip l1 l2)) else None) else None)"
by pat_completeness auto
termination 
  apply (relation "measures [
  (\<lambda>U. card (fv_eqs U)), 
  (\<lambda>U. measure2 U), 
  (\<lambda>U. length U)]")
       apply (auto intro: card_insert_le card_mono psubset_card_mono split: if_split_asm)
  sorry

print_theorems


(******************************** lemmata *********************************)


lemma lambda_simp:  "\<sigma> \<cdot> \<tau> \<cdot> a = (\<lambda>x. \<sigma> \<cdot> \<tau> x) \<cdot> a"
  apply (induction a rule: fv.induct)
  by auto

lemma unifies_sapply_eq [simp]: "unifies \<sigma> (sapply_eq \<tau> eq) \<longleftrightarrow> unifies (\<sigma> \<circ>s \<tau>) eq"
  apply (rule iffI)
  apply (cases eq)
  by (auto simp add: unifies.simps lambda_simp)

lemma unifies_scomp_fst: "unifies a b \<Longrightarrow> unifies (c \<circ>s a) b"
  by (auto simp add: scomp_def unifies.intros unifies.simps lambda_simp[symmetric])

lemma sapply_notin_fv: "\<lbrakk> x \<notin> fv t \<rbrakk> \<Longrightarrow> (Var (x := t)) \<cdot> t = t"
proof (induction t rule: term.induct)
  case (Var x)
  then show ?case by auto
next
  case (Fun x1a x2)
  let ?t = "Fun x1a x2"
  assume 1: "\<And>x2a. x2a \<in> set x2 \<Longrightarrow> x \<notin> fv x2a \<Longrightarrow> Var(x := x2a) \<cdot> x2a = x2a"
  have "Var (x := ?t) \<cdot> ?t = Fun x1a (map (sapply (Var (x := ?t))) x2)" by simp
  moreover have "\<forall>x2s \<in> set x2. x \<notin> fv x2s" using \<open>x \<notin> fv ?t\<close> by simp
  ultimately show ?case by (smt "1" \<open>Var(x := Fun x1a x2) \<cdot> Fun x1a x2 = Fun x1a (map (op \<cdot> (Var(x := Fun x1a x2))) x2)\<close> fun_upd_apply map_idI sapply_cong)
qed

lemma unifies_triv: "\<lbrakk> x \<notin> fv t \<rbrakk> \<Longrightarrow> unifies (Var (x := t)) (Var x, t)"
proof -
  assume "x \<notin> fv t" 
  have "(Var (x := t)) \<cdot> Var x = t" by simp
  moreover have "(Var (x := t)) \<cdot> t = t" using \<open>x \<notin> fv t\<close> by (simp add: sapply_notin_fv)
  ultimately show ?thesis by (simp add: unifies.intros)
qed

lemma unify_notin_fv: "\<lbrakk> x \<notin> fv t \<rbrakk> \<Longrightarrow> unifiess \<sigma> (sapply_eqs (Var (x := t)) xs) \<longleftrightarrow> unifiess (\<sigma> \<circ>s (Var (x := t))) ((Var x, t) # xs)"
  by (auto simp add: unifiess_def unifies_scomp_fst unifies_triv)





lemma unify_return: "unify l = Some \<sigma> \<Longrightarrow> unifiess \<sigma> l"
proof (induction l rule: unify.induct)
  case 1
  then show ?case by (simp only: unifiess_empty)
next
  case (2 x b xs)
  then show ?case
  proof (cases "b = Var x")
    case True
    assume "b = Var x \<Longrightarrow> unify xs = Some \<sigma> \<Longrightarrow> unifiess \<sigma> xs" and "unify ((Var x, b) # xs) = Some \<sigma>"
    then have 1: "unify xs = Some \<sigma> \<Longrightarrow> unifiess \<sigma> xs" using \<open>b = Var x\<close> by blast
    have "unify ((Var x, b) # xs) = unify xs" using \<open>b = Var x\<close> by simp
    then have "unify xs = Some \<sigma>" using \<open>unify ((Var x, b) # xs) = Some \<sigma>\<close> by simp
    then have "unifiess \<sigma> xs" using 1 by blast
    then show ?thesis using \<open>b = Var x\<close> by (simp add: unifiess_list unifies.intros)
  next
    case False
    assume "b \<noteq> Var x \<Longrightarrow> x \<notin> fv b \<Longrightarrow> unify (sapply_eqs (Var(x := b)) xs) = Some \<sigma> \<Longrightarrow> unifiess \<sigma> (sapply_eqs (Var(x := b)) xs)"
       and "unify ((Var x, b) # xs) = Some \<sigma>"
    then show ?thesis
    proof (cases "x \<in> fv b")
      case True 
      assume 1: "unify ((Var x, b) # xs) = Some \<sigma>"
      have "unify ((Var x, b) # xs) = None" using \<open>b \<noteq> Var x\<close> \<open>x \<in> fv b\<close> by simp
      then have False using 1 by simp
      then show ?thesis by blast
    next
      case False
      let ?term = "sapply_eqs (Var(x := b)) xs"
      assume "b \<noteq> Var x \<Longrightarrow> x \<notin> fv b \<Longrightarrow> unify ?term = Some \<sigma> \<Longrightarrow> unifiess \<sigma> ?term"
         and 2: "unify ((Var x, b) # xs) = Some \<sigma>"
      then have 3: "unify ?term = Some \<sigma> \<Longrightarrow> unifiess \<sigma> ?term" using \<open>x \<notin> fv b\<close> \<open>b \<noteq> Var x\<close> by simp
      have "unify ((Var x, b) # xs) =  scomp_opt (unify ?term) (Var (x := b))" using \<open>b \<noteq> Var x\<close> \<open>x \<notin> fv b\<close> by simp
      then have "scomp_opt (unify ?term) (Var (x := b)) = Some \<sigma>" using 2 by simp
      then obtain \<tau> where 4: "unify ?term = Some \<tau>" by (auto dest: scomp_some)
      have "(\<tau> \<circ>s (Var (x := b))) \<cdot> (Var x) = \<tau> \<cdot> b" by (simp)
      also have "... = (\<tau> \<circ>s (Var (x := b))) \<cdot> b" using \<open>x \<notin> fv b\<close> by (simp add: sapply_notin_fv)
      have "unifiess \<tau> ?term" using 3 4 sorry
      then show ?thesis sorry
    qed
  qed
next
  case (3 v va x xs)
  assume 5: "unify ((Var x, Fun v va) # xs) = Some \<sigma> \<Longrightarrow> unifiess \<sigma> ((Var x, Fun v va) # xs)"
     and 6: "unify ((Fun v va, Var x) # xs) = Some \<sigma>"
  have "unify ((Fun v va, Var x) # xs) = unify ((Var x, Fun v va) # xs)" by simp
  then have "unify ((Var x, Fun v va) # xs) = Some \<sigma>" using 6 by simp
  then have 7: "unifiess \<sigma> ((Var x, Fun v va) # xs)" using 5 by simp
  then have "unifies \<sigma> (Fun v va, Var x)" by (simp add: unifies.intros unifies.simps unifiess_def)
  then show ?case using 7 by (auto simp add: unifiess_def) 
next
  case (4 f l1 g l2 xs)
  assume 8: "g = f \<Longrightarrow> length l2 = length l1 \<Longrightarrow> unify (xs @ zip l1 l2) = Some \<sigma> \<Longrightarrow> unifiess \<sigma> (xs @ zip l1 l2)" 
     and 9: "unify ((Fun f l1, Fun g l2) # xs) = Some \<sigma>"
  have 10: "g = f" "length l2 = length l1" "unify (xs @ zip l1 l2) = Some \<sigma>" using 9 by (simp_all split: if_splits)
  then have "unifiess \<sigma> (xs @ zip l1 l2)" using 8 by blast
  then have "unifiess \<sigma> xs" "unifiess \<sigma> (zip l1 l2)" by (auto simp add: unifiess_def)
  then have "\<forall>(a,b) \<in> set (zip l1 l2). unifies \<sigma> (a,b)" by (simp add: unifiess_def)
  then have "\<forall>(a,b) \<in> set (zip l1 l2). \<sigma> \<cdot> a = \<sigma> \<cdot> b" by (simp add: unifies.simps)
  then have "\<sigma> \<cdot> (Fun f l1) = \<sigma> \<cdot> (Fun g l2)" using 10 by (auto intro: unifiess_def)
  then have "unifies \<sigma> (Fun f l1, Fun g l2)" using 10 by simp
  then show ?case by (auto simp add: unifiess_list unifiess_def)
qed

lemma unify_mgu: "\<lbrakk>unify l = Some \<sigma>; unifiess \<tau> l\<rbrakk> \<Longrightarrow> \<exists> \<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
proof (induction l rule: unify.induct)
  case 1
  have "unify [] = Some Var" by simp
  then have "\<sigma> = Var" using \<open>unify [] = Some \<sigma>\<close> by simp
  then have "\<tau> = \<tau> \<circ>s \<sigma>" by simp
  then show ?case by (rule exI[where ?x = \<tau>])
next
case (2 x b xs)
  then show ?case sorry
next
  case (3 v va x xs)
  assume 1: "unify ((Var x, Fun v va) # xs) = Some \<sigma> \<Longrightarrow> unifiess \<tau> ((Var x, Fun v va) # xs) \<Longrightarrow> \<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
     and 2: "unify ((Fun v va, Var x) # xs) = Some \<sigma>"
     and "unifiess \<tau> ((Fun v va, Var x) # xs)"
  then have "unifiess \<tau> ((Var x, Fun v va) # xs)" by (simp add: unifiess_def unifies.simps)
  moreover have "unify ((Var x, Fun v va) # xs) = Some \<sigma>" using 2 by simp
  ultimately have "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>" using 1 by simp
then show ?case .
next
  case (4 f l1 g l2 xs)
  assume "g = f \<Longrightarrow> length l2 = length l1 \<Longrightarrow> unify (xs @ zip l1 l2) = Some \<sigma> \<Longrightarrow> unifiess \<tau> (xs @ zip l1 l2) \<Longrightarrow> \<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
     and "unify ((Fun f l1, Fun g l2) # xs) = Some \<sigma>"
     and 3: "unifiess \<tau> ((Fun f l1, Fun g l2) # xs)"
  then have "f = g" "length l1 = length l2" "unify (xs @ zip l1 l2) = Some \<sigma>" by (simp_all split: if_splits)
  have "unifiess \<tau> xs" "unifies \<tau> (Fun f l1, Fun g l2)" using 3 by (auto simp add: unifiess_def)
  have "unifiess \<tau> (xs @ zip l1 l2)" using 3 by simp
  then show ?case sorry
qed


lemma unify_sound: "unify l = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> l"
  by (auto simp add: unify_mgu unify_return)


lemma unifier_exists_unify: "\<exists>\<tau>. unifiess \<tau> l \<Longrightarrow> \<exists>\<sigma>. unify l = Some \<sigma>"
proof (induction l rule: unify.induct)
  case 1
  have "unify [] = Some Var" by simp
  then show ?case by (rule exI[where ?x = Var])
next
case (2 x b xs)
  then show ?case
  proof (cases "b = Var x")
    case True
    assume 1: "b = Var x \<Longrightarrow> \<exists>\<tau>. unifiess \<tau> xs \<Longrightarrow> \<exists>\<sigma>. unify xs = Some \<sigma>"
       and "\<exists>\<tau>. unifiess \<tau> ((Var x, b) # xs)"
    then obtain \<tau> where "unifiess \<tau> ((Var x, b) # xs)" by auto
    then have "unifiess \<tau> xs" by (auto simp add: unifiess_def)
    then have "\<exists>\<tau>. unifiess \<tau> xs" by blast
    then have "\<exists>\<sigma>. unify xs = Some \<sigma>" using \<open>b = Var x\<close> 1 by simp
    have "unify ((Var x, b) # xs) = unify xs" using \<open>b = Var x\<close> by simp 
    then show ?thesis using \<open>\<exists>\<sigma>. unify xs = Some \<sigma>\<close> by simp
  next
    case False
    then show ?thesis sorry
  qed
next
case (3 v va x xs)
then show ?case sorry
next
  case (4 f l1 g l2 xs)
  then show ?case sorry
qed

lemma unify_complete: "\<exists> \<sigma>. unifiess \<sigma> l \<Longrightarrow> (\<exists>\<tau>. unify l = Some \<tau> \<and> unifiess \<tau> l)"
proof -
  assume "\<exists> \<sigma>. unifiess \<sigma> l"
  then have "\<exists>\<rho>. unify l = Some \<rho>" by (simp add: unifier_exists_unify)
  then obtain x where 1: "unify l = Some x" by auto
  then have "unifiess x l" using 1 by (simp add: unify_return)
  then have "unify l = Some x \<and> unifiess x l" using 1 by simp
  then show ?thesis by (rule exI[where ?x = x])
qed


lemma 3:
  fixes \<sigma> :: "('f, 'v) subst" 
    and l :: "('f, 'v) equations"
  assumes 1: "unify l = Some \<sigma>"
  shows subst_subs: "fv_eqs (sapply_eqs \<sigma> l) \<subseteq> fv_eqs l"
    and sdom_fv: "sdom \<sigma> \<subseteq> fv_eqs l"
    and svran_fv: "svran \<sigma> \<subseteq> fv_eqs l"
    and sdom_svran_disj: "sdom \<sigma> \<inter> svran \<sigma> = {}"
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

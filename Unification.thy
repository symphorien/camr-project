chapter {* camr project *}

theory Unification imports Main begin


(****************************** ( 1A ) ******************************)

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

fun fv :: "('f, 'v) term \<Rightarrow> 'v set" where
  "fv (Var x) = {x}"
| "fv (Fun f xs) = (\<Union>x \<in> (set xs). fv x)"

(****************************** ( 1B ) ******************************)
type_synonym ('f, 'v) subst = "'v \<Rightarrow> ('f, 'v) term"

fun sapply :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixr "\<cdot>" 67) where 
  "sapply \<sigma> (Var x) = \<sigma> x"
| "sapply \<sigma> (Fun g xs) = Fun g (map (sapply \<sigma>) xs)"

definition scomp :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst" (infixl "\<circ>s" 75) where
  "scomp \<sigma> \<tau> = (\<lambda>x. \<sigma> \<cdot> (\<tau> x))"

lemma sapply_sapply: "a \<cdot> b \<cdot> t = (scomp a b) \<cdot> t"
  by(induction t,simp_all add:scomp_def)


(********************************* size argument ****************************)
(* The following section contains lemmas used to show the completeness of Robinson's algorithm 
further down. The main lemma proved is in_fv_not_unifies, stating that there can't be a unifier
for ((Var x, b) # xs) is x \<in> fv b *)

fun msize :: "('f, 'v) term \<Rightarrow> nat" where
  "msize (Var x) = 1"
| "msize (Fun f xs) = 1 + sum_list (map msize xs)"

inductive ssube :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "\<lbrakk> x \<in> set xs \<or> (\<exists>y \<in> set xs. ssube x y) \<rbrakk> \<Longrightarrow> ssube x (Fun f xs)"


lemma ssube_size: "ssube e1 e2 \<Longrightarrow> msize e1 < msize e2"
proof (induction e1 e2 rule: ssube.induct)
  case (1 x xs f)
  then show ?case 
  proof (rule disjE)
    assume "x \<in> set xs"
    then have "msize x \<in> set (map msize xs)" by auto
    then have 2: "msize x \<le> sum_list (map msize xs)" by (auto simp add: member_le_sum_list)
    have "msize (Fun f xs) = 1 + sum_list (map msize xs)" by simp
    then show "msize x < msize (Fun f xs)" using 2 by auto
  next
    assume "\<exists>y\<in>set xs. ssube x y \<and> msize x < msize y"
    then obtain y where 3: "y \<in> set xs \<and> ssube x y \<and> msize x < msize y" by blast
    then have "msize y \<in> set (map msize xs)" by auto
    then have 4: "msize y \<le> sum_list (map msize xs)" by (auto simp add: member_le_sum_list)
    have "msize (Fun f xs) = 1 + sum_list (map msize xs)" by simp
    then show "msize x < msize (Fun f xs)" using 3 4 by auto
  qed
qed

lemma msize_term_diff: "\<lbrakk> msize a \<noteq> msize b \<rbrakk> \<Longrightarrow> a \<noteq> b"
  apply (rule notI)
  by (auto)

lemma msize_gt_zero: "msize x > 0"
  apply (cases x)
  by (auto)

lemma ssube_subst_stable: "ssube e1 e2 \<Longrightarrow> ssube (\<sigma> \<cdot> e1) (\<sigma> \<cdot> e2)"
proof (induction e1 e2 rule: ssube.induct)
  case (1 x xs f)
  then show ?case
  proof (rule disjE)
    assume "x \<in> set xs"
    then have "\<sigma> \<cdot> x \<in> set (map (sapply \<sigma>) xs)" by auto
    then have "ssube (\<sigma> \<cdot> x) (Fun f (map (sapply \<sigma>) xs))" by (auto intro: ssube.intros)
    then show ?thesis by simp
  next
    assume "\<exists>y\<in>set xs. ssube x y \<and> ssube (\<sigma> \<cdot> x) (\<sigma> \<cdot> y)" 
    then obtain y where 2: "y \<in> set xs \<and> ssube x y \<and> ssube (\<sigma> \<cdot> x) (\<sigma> \<cdot> y)" by blast
    then have "\<sigma> \<cdot> y \<in> set (map (sapply \<sigma>) xs)" by auto
    then show ?thesis using 2 by (auto intro: ssube.intros)
  qed
qed

lemma fv_ssube: "\<lbrakk> x \<in> fv b; b \<noteq> Var x \<rbrakk> \<Longrightarrow> (ssube (Var x) b)"
  by (induction b) (auto intro: ssube.intros)

lemma fv_msize_diff: "\<lbrakk> x \<in> fv b; b \<noteq> Var x \<rbrakk> \<Longrightarrow> msize (Var x) < msize b"
proof -
  assume 1: "x \<in> fv b" "b \<noteq> Var x"
  then have "ssube (Var x) b" by (simp add: fv_ssube)
  then show ?thesis using ssube_size by fastforce
qed

lemma fv_msize_sapply_diff: "\<lbrakk> x \<in> fv b; b \<noteq> Var x \<rbrakk> \<Longrightarrow> msize (\<sigma> x) < msize (\<sigma> \<cdot> b)"
proof -
  assume "x \<in> fv b" and "b \<noteq> Var x"
  then have "ssube (Var x) b" by (simp add: fv_ssube)
  then have "ssube (\<sigma> x) (\<sigma> \<cdot> b)" using ssube_subst_stable by fastforce
  then show ?thesis using ssube_size by fastforce
qed


(****************************** ( 1C ) ******************************)
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


(****************************** ( 1D ) ******************************)
(* definitions *)

definition sdom :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "sdom \<sigma> = {x | x. \<sigma> x \<noteq> Var x}"

definition sran :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set" where
  "sran \<sigma> = {\<sigma> x | x. x \<in> sdom \<sigma>}"

definition svran :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "svran \<sigma> = (\<Union> t \<in> sran \<sigma>. fv t)"

(* helpers *)
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

(* lemmata *)
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


(****************************** ( 2 ) ******************************)
type_synonym ('f, 'v) equation = "('f, 'v) term \<times> ('f, 'v) term"

type_synonym ('f, 'v) equations = "('f, 'v) equation list"

fun fv_eq :: "('f, 'v) equation \<Rightarrow> 'v set" where
  "fv_eq (a, b) = fv a \<union> fv b"

fun fv_eqs :: "('f, 'v) equations \<Rightarrow> 'v set" where
  "fv_eqs l = (\<Union>x \<in> set l. fv_eq x)"

fun sapply_eq :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> ('f, 'v) equation" where
  "sapply_eq \<sigma> (a,b) = (sapply \<sigma> a, sapply \<sigma> b)"

fun sapply_eqs :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> ('f, 'v) equations" where
  "sapply_eqs \<sigma> l = map (sapply_eq \<sigma>) l"


(****************************** ( 2A ) ******************************)
lemma fv_sapply_eq: "fv_eq (sapply_eq \<sigma> (a,b)) = fv (\<sigma> \<cdot> a) \<union> fv (\<sigma> \<cdot> b)"
  by auto

lemma fv_sapply_eqs: "fv_eqs (sapply_eqs \<sigma> l) = (\<Union>x \<in> set l. fv_eq (sapply_eq \<sigma> x))"
  by (auto)

lemma sapply_scomp_distrib_eq: "sapply_eq (\<sigma> \<circ>s \<tau>) (a,b) = (\<sigma> \<cdot> (\<tau> \<cdot> a), \<sigma> \<cdot> (\<tau> \<cdot> b))"
  by (simp)

lemma sapply_scomp_distrib_eqs: "sapply_eqs (\<sigma> \<circ>s \<tau>) l = map (\<lambda>x. sapply_eq (\<sigma> \<circ>s \<tau>) x) l"
  apply (induction l)
  by auto

(* helpers used for lemma 3 *)
lemma fv_sapply_eq_sdom_svran: "x \<in> fv_eq (sapply_eq \<sigma> t) \<Longrightarrow> x \<in> (fv_eq t - sdom \<sigma>) \<union> svran \<sigma>"
proof -
  assume "x \<in> fv_eq (sapply_eq \<sigma> t)"
  moreover obtain a b where "t = (a,b)" using fv_eq.cases by blast
  ultimately have "x \<in> fv (\<sigma> \<cdot> a) \<union> fv (\<sigma> \<cdot> b)" by auto
  then have "x \<in> (fv a - sdom \<sigma>) \<union> svran \<sigma> \<union> (fv b - sdom \<sigma>) \<union> svran \<sigma>" using fv_sapply_sdom_svran by (metis Un_iff)
  then have "x \<in> (fv a \<union> fv b - sdom \<sigma>) \<union> svran \<sigma>" by blast
  then show ?thesis by (simp add: \<open>t = (a, b)\<close>)
qed

lemma fv_sapply_eqs_sdom_svran: "x \<in> fv_eqs (sapply_eqs \<sigma> t) \<Longrightarrow> x \<in> (fv_eqs t - sdom \<sigma>) \<union> svran \<sigma>"
proof -
  assume "x \<in> fv_eqs (sapply_eqs \<sigma> t)"
  then have "x \<in> (\<Union>y \<in> set t. fv_eq (sapply_eq \<sigma> y))" by (auto simp add: fv_sapply_eqs)
  then have "x \<in> (\<Union>y \<in> set t. fv_eq y - sdom \<sigma>) \<union> svran \<sigma>" using fv_sapply_eq_sdom_svran by (metis (no_types, lifting) UN_iff UnE UnI1 UnI2)
  then show ?thesis by auto 
qed

lemma fv_sapply_var: "\<lbrakk> b \<noteq> Var x \<rbrakk> \<Longrightarrow> fv_eqs (sapply_eqs (Var (x := b)) xs) \<subseteq> fv b \<union> fv_eqs xs"
proof (rule subsetI)
  fix y
  assume "b \<noteq> Var x"
  then have "svran (Var (x := b)) = fv b" by simp
  then show "y \<in> fv_eqs (sapply_eqs (Var(x := b)) xs) \<Longrightarrow> y \<in> fv b \<union> fv_eqs xs" using fv_sapply_eqs_sdom_svran by (metis Diff_iff UnE UnI1 UnI2)
qed


(****************************** ( 2B ) ******************************)
inductive unifies :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "\<lbrakk> \<sigma> \<cdot> a = \<sigma> \<cdot> b \<rbrakk> \<Longrightarrow> unifies \<sigma> (a, b)"

definition unifiess :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "unifiess \<sigma> l =  (\<forall> x \<in> set l. unifies \<sigma> x)"

(* some helper lemmas about unifies / unifiess *)
lemma unifiess_empty: "unifiess \<sigma> []"
  by (auto simp add: unifiess_def)

lemma unifiess_list: "\<lbrakk> unifies \<sigma> x; unifiess \<sigma> xs \<rbrakk> \<Longrightarrow> unifiess \<sigma> (x # xs)"
  by (auto simp add: unifies.intros unifiess_def)

lemma unifies_zip: "\<lbrakk> length l1 = length l2; (\<And>a b. (a,b) \<in> set (zip l1 l2) \<Longrightarrow> unifies \<sigma> (a,b)) \<rbrakk> \<Longrightarrow> unifiess \<sigma> (zip l1 l2)"
  apply (induction "zip l1 l2")
  by (auto simp add: unifiess_def)

lemma in_fv_not_unifies: "\<lbrakk> x \<in> fv b; b \<noteq> Var x \<rbrakk> \<Longrightarrow> \<not>(\<exists>\<sigma>. unifies \<sigma> (Var x, b))"
proof (rule notI)
  assume 1: "x \<in> fv b"
     and 2: "b \<noteq> Var x"
     and 3: "\<exists>\<sigma>. unifies \<sigma> (Var x, b)"
  then obtain \<sigma> where "unifies \<sigma> (Var x, b)" by blast
  then have "\<sigma> x = \<sigma> \<cdot> b" by (auto simp add: unifies.simps)
  then show "False"
  proof (cases b)
    case (Var x1)
    have "fv b = {x1}" using \<open>b = Var x1\<close> by simp
    then have "x1 = x" using \<open>x \<in> fv b\<close> by simp
    then have "b = Var x" using \<open>b = Var x1\<close> by simp
    then show ?thesis using \<open>b \<noteq> Var x\<close> by simp
  next
    case (Fun f xs)
    obtain \<sigma> where "unifies \<sigma> (Var x, b)" using 3 by blast
    then have "\<sigma> x = \<sigma> \<cdot> b" by (simp add: unifies.simps)
    have "msize (\<sigma> x) < msize (\<sigma> \<cdot> b)" using 1 2 by (simp add: fv_msize_sapply_diff)
    then have "\<sigma> x \<noteq> \<sigma> \<cdot> b" by (simp add: msize_term_diff)
    then have False using \<open>\<sigma> x = \<sigma> \<cdot> b\<close> by blast
    then show ?thesis by simp
  qed
qed

lemma length_zip: "\<lbrakk> length l1 = length l2 \<rbrakk> \<Longrightarrow> (\<forall>(a,b) \<in> set (zip l1 l2). f a = f b) \<longleftrightarrow> map f l1 = map f l2"
proof (induction l1 l2 rule: list_induct2)
  case Nil
  then show ?case by auto
next
  case (Cons x xs y ys)
  then show ?case by auto
qed

lemma unify_zip_fun: "\<lbrakk> length l1 = length l2 \<rbrakk> \<Longrightarrow> unifiess \<sigma> (zip l1 l2) \<longleftrightarrow> unifies \<sigma> (Fun f l1, Fun f l2)"
proof (rule iffI)
  assume "length l1 = length l2"
     and "unifiess \<sigma> (zip l1 l2)"
  then have "\<forall>(a,b) \<in> set (zip l1 l2). \<sigma> \<cdot> a = \<sigma> \<cdot> b" by (auto simp add: unifiess_def unifies.simps)
  then have "map (sapply \<sigma>) l1 = map (sapply \<sigma>) l2" using \<open>length l1 = length l2\<close> by (simp add: length_zip)
  then have "\<sigma> \<cdot> (Fun f l1) = \<sigma> \<cdot> (Fun f l2)" by auto
  then show  "unifies \<sigma> (Fun f l1, Fun f l2)" using unifies.intros by blast
next
  assume "length l1 = length l2"
     and "unifies \<sigma> (Fun f l1, Fun f l2)"
  then have "\<sigma> \<cdot> (Fun f l1) = \<sigma> \<cdot> (Fun f l2)" by (auto simp add: unifies.simps)
  then have "map (sapply \<sigma>) l1 = map (sapply \<sigma>) l2" by auto
  then have "\<forall>(a,b) \<in> set (zip l1 l2). \<sigma> \<cdot> a = \<sigma> \<cdot> b" using \<open>length l1 = length l2\<close> by (simp add: length_zip)
  then show "unifiess \<sigma> (zip l1 l2)" using \<open>length l1 = length l2\<close> unifies_zip unifies.intros by fastforce
qed

lemma ex_unifier_fun: 
  assumes "(\<exists>\<tau>. unifiess \<tau> ((Fun f l1, Fun g l2) # xs))"
  shows "f = g"
    and "length l1 = length l2"
    and "\<exists>\<tau>. unifiess \<tau> (xs @ zip l1 l2)"
proof -
  obtain \<tau> where "unifiess \<tau> ((Fun f l1, Fun g l2) # xs)" using assms by auto
  then have "unifies \<tau> (Fun f l1, Fun g l2)" by (simp add: unifiess_def)
  then have "Fun f (map (sapply \<tau>) l1) = Fun g (map (sapply \<tau>) l2)" by (auto simp add: unifies.simps)
  then show "f = g" by simp
next
  obtain \<tau> where 3: "unifiess \<tau> ((Fun f l1, Fun g l2) # xs)" using assms by auto
  then have 1: "unifies \<tau> (Fun f l1, Fun g l2)" by (simp add: unifiess_def)
  then have "Fun f (map (sapply \<tau>) l1) = Fun g (map (sapply \<tau>) l2)" by (auto simp add: unifies.simps)
  then have "map (sapply \<tau>) l1 = map (sapply \<tau>) l2" by simp
  then show 2: "length l1 = length l2" using map_eq_imp_length_eq by blast
  have "unifiess \<tau> (zip l1 l2)" using 1 2 unify_zip_fun[OF 2] \<open>Fun f (map (op \<cdot> \<tau>) l1) = Fun g (map (op \<cdot> \<tau>) l2)\<close> by blast
  moreover have "unifiess \<tau> xs" using 3 by (auto simp add: unifiess_def)
  ultimately have "unifiess \<tau> (xs @ zip l1 l2)" by (auto simp add: unifiess_def)
  then show "\<exists>\<tau>. unifiess \<tau> (xs @ zip l1 l2)" by blast
qed

(* end of helper lemmas *)

fun is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "is_mgu \<sigma> l \<longleftrightarrow> (unifiess \<sigma> l \<and> (\<forall> \<tau>. unifiess \<tau> l \<longrightarrow> (\<exists> \<rho>. \<tau> = \<rho> \<circ>s \<sigma>)))"


(****************************** ( 2C ) ******************************)
lemma lambda_simp:  "\<sigma> \<cdot> \<tau> \<cdot> a = (\<lambda>x. \<sigma> \<cdot> \<tau> x) \<cdot> a"
  apply (induction a rule: fv.induct)
  by auto

lemma unifies_sapply_eq [simp]: "unifies \<sigma> (sapply_eq \<tau> eq) \<longleftrightarrow> unifies (\<sigma> \<circ>s \<tau>) eq"
  apply (rule iffI)
  apply (cases eq)
  by (auto simp add: unifies.simps lambda_simp)

lemma unifiess_sapply_eqs [simp]: "unifiess \<sigma> (sapply_eqs \<tau> eqs) \<longleftrightarrow> unifiess (\<sigma> \<circ>s \<tau>) eqs"
  apply (induction eqs)
  apply (auto simp add: unifiess_def lambda_simp) 
  by (metis (no_types, lifting) Unification.scomp_def sapply_cong unifies.simps)+


(**** UNIFY ALGORITHM **** UNIFY ALGORITHM **** UNIFY ALGORITHM **** UNIFY ALGORITHM ****)

(* helper function for robinson algorithm *)
fun scomp_opt :: "('f, 'v) subst option \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst option" where
  "scomp_opt (Some \<sigma>) \<tau> = Some (\<sigma> \<circ>s \<tau>)"
| "scomp_opt None _ = None"

(* measure function to show termination of robinson *)
fun size_exp :: "('f, 'v) term \<Rightarrow> nat" where
  "size_exp (Var _) = 0"
| "size_exp (Fun _ l) = 1 + sum_list (map size_exp l)"

fun eqs_size :: "('f, 'v) equations \<Rightarrow> nat" where
  "eqs_size [] = 0"
| "eqs_size ((e, _) # eqs) = size_exp e + eqs_size eqs"

(* helper lemmas to show termination of robinson *)
lemma eqs_size_append: "eqs_size (xs @ ys) = eqs_size xs + eqs_size ys"
  apply (induction xs)
  by auto

lemma eqs_size_zip [simp]: "\<lbrakk> length l1 = length l2 \<rbrakk> \<Longrightarrow> eqs_size (xs @ zip l1 l2) = eqs_size xs + sum_list (map size_exp l1)"
proof (induction l1 l2 rule: list_induct2) 
  case Nil
  then show ?case by auto
next
  case (Cons x xs y ys)
  then show ?case by (auto simp add: eqs_size_append)
qed

lemma scomp_some: "scomp_opt a b = Some c \<Longrightarrow> \<exists>\<sigma>. a = Some \<sigma>"
  apply (cases a)
  by auto

lemma finite_fv [simp]: "finite (fv e)"
  apply (induction e)
  by auto

lemma finite_fv_eq [simp]: "finite (fv_eq e)"
  apply (cases e)
  by auto

lemma finite_fv_eqs [simp]: "finite (fv_eqs l)"
  apply (induction l)
  by (auto)

lemma fv_eqs_cons [simp]: "fv_eqs (eq # eqs) = fv_eq eq \<union> fv_eqs eqs"
  by (auto) 

lemma fv_eq_subst_eq: "fv_eq (sapply_eq \<sigma> eq) = (\<Union>x\<in>fv_eq eq. fv (\<sigma> x))"
  by(cases eq)(simp add: fv_sapply)

lemma fv_eqs_subst_eqs: "fv_eqs (map (sapply_eq \<sigma>) eqs) = (\<Union> x\<in>fv_eqs eqs. fv (\<sigma> x))"
  by(simp add: fv_eq_subst_eq)

lemma fv_eqs_zip [simp]: "\<lbrakk> length l1 = length l2 \<rbrakk> \<Longrightarrow> fv_eqs (xs @ zip l1 l2) = (\<Union>x\<in>set l1. fv x) \<union> (\<Union>x\<in>set l2. fv x) \<union> fv_eqs xs"
  apply (induction l1 l2 rule: list_induct2)
  by (auto)

(****************************** ( 3A ) ******************************)
function (sequential) unify :: "('f, 'v) equations \<Rightarrow> ('f, 'v) subst option" where
  "unify [] = Some Var"
| "unify ((Var x, b) # xs) = (if b = Var x then unify xs else (if x \<in> fv b then None else scomp_opt (unify (sapply_eqs (Var (x := b)) xs)) (Var (x := b))))"
| "unify ((b, Var x) # xs) = unify ((Var x, b) # xs)"
| "unify ((Fun f l1, Fun g l2) # xs) = (if g = f then (if length l2 = length l1 then unify (xs @ (zip l1 l2)) else None) else None)"
by pat_completeness auto
termination
  apply (relation "measures [
  (\<lambda>U. card (fv_eqs U)), eqs_size, length]") 
  by (auto intro!: psubset_card_mono card_mono split: if_split_asm simp add: fv_eqs_subst_eqs simp del: fv_eqs.simps) 


(* helper lemmas to show soundness and or completeness *)
lemma unifies_scomp_fst: "unifies a b \<Longrightarrow> unifies (c \<circ>s a) b"
  by (auto simp add: scomp_def unifies.intros unifies.simps lambda_simp[symmetric])

lemma sapply_notin_fv: "\<lbrakk> x \<notin> fv t \<rbrakk> \<Longrightarrow> (Var (x := s)) \<cdot> t = t"
proof (induction t arbitrary: s rule: term.induct)
  case (Var x)
  then show ?case by auto
next
  case 2: (Fun f xs)
  have "x \<notin> (\<Union>y \<in> (set xs). fv y)" using \<open>x \<notin> fv (Fun f xs)\<close> by simp
  then have "(\<forall>y \<in> (set xs). x \<notin> fv y)" by simp
  then have "(\<forall>y \<in> (set xs). (Var (x := Fun f xs)) \<cdot> y = y)" using 2 by blast
  moreover have "Var (x := (Fun f xs)) \<cdot> (Fun f xs) = Fun f (map (sapply (Var (x := Fun f xs))) xs)" by simp
  ultimately show ?case by (metis "2.IH" \<open>\<forall>y\<in>set xs. x \<notin> fv y\<close> map_idI sapply.simps(2))
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

lemma unifier_invariant: "\<lbrakk> x \<notin> fv b; unifies \<tau> (Var x, b) \<rbrakk> \<Longrightarrow> \<tau> \<circ>s (Var (x := b)) = \<tau>"
proof (rule ext)
  assume "x \<notin> fv b" and "unifies \<tau> (Var x, b)"
  fix xa
  show "(\<tau> \<circ>s (Var (x := b))) xa = \<tau> xa" 
  proof (cases "xa = x")
    case True
    have "(\<tau> \<circ>s (Var (x := b))) xa = \<tau> \<cdot> b" using \<open>xa = x\<close> by simp
    then have "... = \<tau> x" using \<open>unifies \<tau> (Var x, b)\<close> by (simp add: unifies.simps)
    then show ?thesis by simp
  next
    case False
    have "(\<tau> \<circ>s (Var (x := b))) xa = \<tau> xa" using \<open>xa \<noteq> x\<close> by simp
    then show ?thesis by simp
  qed 
qed

lemma unify_notin_fv_spec:
  assumes "x \<notin> fv t"
      and "unifiess \<sigma> ((Var x, t) # xs)"
    shows "unifiess \<sigma> (sapply_eqs (Var (x := t)) xs)"
  apply (simp add: unifiess_def)
proof (safe)
  fix a b
  assume "(a, b) \<in> set xs"
  have "unifies \<sigma> (Var x, t)" using assms by (simp add: unifiess_def)
  then have "\<sigma> \<circ>s (Var (x := t)) = \<sigma>" using assms by (simp add: unifier_invariant)
  moreover have "unifies \<sigma> (a, b)" using \<open>(a,b) \<in> set xs\<close>  assms by (simp add: unifiess_def) 
  ultimately show "unifies (\<sigma> \<circ>s Var(x := t)) (a, b)" by simp
qed


lemma unify_notin: "\<lbrakk> unify ((Var x, b) # xs) = Some \<sigma>;  b \<noteq> Var x \<rbrakk> \<Longrightarrow> x \<notin> fv b"
  by auto


(**** SOUNDNESS **** SOUNDNESS **** SOUNDNESS **** SOUNDNESS **** SOUNDNESS ****)

lemma unify_return: "unify l = Some \<sigma> \<Longrightarrow> unifiess \<sigma> l"
proof (induction l arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by (simp only: unifiess_empty)
next
  case Var_Var: (2 x b xs)
  then show ?case
  proof (cases "b = Var x")
    case True 
    then have 1: "unify xs = Some \<sigma> \<Longrightarrow> unifiess \<sigma> xs" using \<open>b = Var x\<close> using Var_Var by blast
    have "unify ((Var x, b) # xs) = unify xs" using \<open>b = Var x\<close> by simp
    then have "unify xs = Some \<sigma>" using \<open>unify ((Var x, b) # xs) = Some \<sigma>\<close> by simp
    then have "unifiess \<sigma> xs" using 1 by blast
    then show ?thesis using \<open>b = Var x\<close> by (simp add: unifiess_list unifies.intros)
  next 
    case False
    have "x \<notin> fv b" using unify_notin Var_Var False by auto 
    let ?term = "sapply_eqs (Var(x := b)) xs"
    have 3: "unify ?term = Some \<sigma> \<Longrightarrow> unifiess \<sigma> ?term" using Var_Var \<open>x \<notin> fv b\<close> \<open>b \<noteq> Var x\<close> by simp
    have "unify ((Var x, b) # xs) =  scomp_opt (unify ?term) (Var (x := b))" using \<open>b \<noteq> Var x\<close> \<open>x \<notin> fv b\<close> by simp
    then have "scomp_opt (unify ?term) (Var (x := b)) = Some \<sigma>" using Var_Var by simp
    then obtain \<tau> where 4: "unify ?term = Some \<tau>" by (auto dest: scomp_some)
    have "(\<tau> \<circ>s (Var (x := b))) \<cdot> (Var x) = \<tau> \<cdot> b" by (simp)
    also have "... = (\<tau> \<circ>s (Var (x := b))) \<cdot> b" using \<open>x \<notin> fv b\<close> by (simp add: sapply_notin_fv)
    have "unifiess \<tau> ?term" using 3 4 False Var_Var.IH(2) \<open>x \<notin> fv b\<close> by force
    then show ?thesis using Var_Var "4" False \<open>scomp_opt (unify (sapply_eqs (Var(x := b)) xs)) (Var(x := b)) = Some \<sigma>\<close> unify_notin_fv by fastforce 
  qed
next
  case (3 v va x xs)
  have "unify ((Fun v va, Var x) # xs) = unify ((Var x, Fun v va) # xs)" by simp
  then have "unify ((Var x, Fun v va) # xs) = Some \<sigma>" using 3 by simp
  then have 7: "unifiess \<sigma> ((Var x, Fun v va) # xs)" using 3 by simp
  then have "unifies \<sigma> (Fun v va, Var x)" by (simp add: unifies.intros unifies.simps unifiess_def)
  then show ?case using 7 by (auto simp add: unifiess_def) 
next
  case (4 f l1 g l2 xs)
  have 10: "g = f" "length l2 = length l1" "unify (xs @ zip l1 l2) = Some \<sigma>" using 4 by (simp_all split: if_splits)
  then have "length l1 = length l2" using 4 by simp
  have "unifiess \<sigma> (xs @ zip l1 l2)" using 4 10 by blast
  then have "unifiess \<sigma> xs" "unifiess \<sigma> (zip l1 l2)" by (auto simp add: unifiess_def)
  then have "unifies \<sigma> (Fun f l1, Fun g l2)" using \<open>unifiess \<sigma> (zip l1 l2)\<close> unify_zip_fun[OF \<open>length l1 = length l2\<close>] using "10"(1) by blast
  then show ?case using \<open>unifiess \<sigma> xs\<close> by (auto simp add: unifiess_list unifiess_def)
qed


lemma unify_mgu: "\<lbrakk>unify l = Some \<sigma>; unifiess \<tau> l\<rbrakk> \<Longrightarrow> \<exists> \<rho>. \<tau> = \<rho> \<circ>s \<sigma>"
proof (induction l arbitrary: \<sigma> \<tau> rule: unify.induct)
  case 1
  have "unify [] = Some Var" by simp
  then have "\<sigma> = Var" using \<open>unify [] = Some \<sigma>\<close> by simp
  then have "\<tau> = \<tau> \<circ>s \<sigma>" by simp
  then show ?case by (rule exI[where ?x = \<tau>])
next
  case (2 x b xs)
  then show ?case
  proof (cases "b = Var x")
    case b_var: True
    then have "unify ((Var x, b) # xs) = unify xs" by simp
    then have "unify xs = Some \<sigma>" using 2 by simp
    moreover have "unifiess \<tau> xs" using 2 by (simp add: unifiess_def)
    ultimately have "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>" using \<open>b = Var x\<close> 2 by blast
    then show ?thesis .
  next
    case b_fun: False
    then have x_free: "x \<notin> fv b" using 2 b_fun unify_notin by auto
    let ?term = "sapply_eqs (Var(x := b)) xs"
    have "unify ((Var x, b) # xs) = scomp_opt (unify ?term) (Var (x := b))" using x_free b_fun by simp
    then have 3: "scomp_opt (unify ?term) (Var (x := b)) = Some \<sigma>" using 2 by simp
    then have "\<exists>\<tau>. unify ?term = Some \<tau>" by (auto simp add: scomp_some)
    then obtain \<sigma>\<^sub>2 where 4: "unify ?term = Some \<sigma>\<^sub>2" by blast
    moreover have "unifiess \<tau> ?term" using 2 \<open>x \<notin> fv b\<close> unify_notin_fv_spec by auto
    ultimately have "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>\<^sub>2" using 2 \<open>x \<notin> fv b\<close> \<open>b \<noteq> Var x\<close> by blast
    then show ?thesis by (metis "2.prems"(2) "3" "4" list.set_intros(1) option.inject scomp_assoc scomp_opt.simps(1) unifier_invariant unifiess_def x_free)
  qed
next
  case (3 v va x xs)
  then have "unifiess \<tau> ((Var x, Fun v va) # xs)" by (simp add: unifiess_def unifies.simps)
  moreover have "unify ((Var x, Fun v va) # xs) = Some \<sigma>" using 3 by simp
  ultimately have "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>" using 3 by blast
then show ?case .
next
  case Fun_Case: (4 f l1 g l2 xs)
  then have 5: "f = g" "length l1 = length l2" "unify (xs @ zip l1 l2) = Some \<sigma>" by (simp_all split: if_splits)
  have "unifiess \<tau> xs" "unifies \<tau> (Fun f l1, Fun g l2)" using Fun_Case by (auto simp add: unifiess_def)
  then have "unifiess \<tau> (zip l1 l2)" using Fun_Case unify_zip_fun[OF \<open>length l1 = length l2\<close>] \<open>f = g\<close> by blast
  then have "unifiess \<tau> (xs @ zip l1 l2)" using \<open>unifiess \<tau> xs\<close> by (auto simp add: unifiess_def)
  then have "\<exists>\<rho>. \<tau> = \<rho> \<circ>s \<sigma>" using Fun_Case 5 by (simp add: Fun_Case.IH) 
  then show ?case .
qed


lemma unify_sound: "unify l = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> l"
  by (auto simp add: unify_mgu unify_return)


(**** COMPLETENESS **** COMPLETENESS **** COMPLETENESS **** COMPLETENESS ****)


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
    case b_notvar: False
    then show ?thesis
    proof (cases "x \<in> fv b")
      case True
      obtain \<tau> where "unifiess \<tau> ((Var x, b) # xs)" using 2 by blast
      then have "unifies \<tau> (Var x, b)" by (simp add: unifiess_def)
      then have "\<exists>\<tau>. unifies \<tau> (Var x, b)" by blast
      moreover have "\<nexists>\<tau>. unifies \<tau> (Var x, b)" using \<open>x \<in> fv b\<close> \<open>b \<noteq> Var x\<close> by (simp add: in_fv_not_unifies)
      ultimately have False by simp
      then show ?thesis by simp
    next
      let ?term = "(sapply_eqs (Var(x := b)) xs)"
      case x_free: False
      obtain \<tau> where "unifiess \<tau> ((Var x, b) # xs)" using 2 by blast 
      then have "unifiess \<tau> ?term" using \<open>x \<notin> fv b\<close>  unify_notin_fv_spec by simp
      then have "\<exists>\<sigma>. unify (sapply_eqs (Var(x := b)) xs) = Some \<sigma>" using 2 \<open>x \<notin> fv b\<close> \<open>b \<noteq> Var x\<close> by blast
      then obtain \<sigma> where "unify (sapply_eqs (Var(x := b)) xs) = Some \<sigma>" by blast
      moreover have "unify ((Var x, b) # xs) = scomp_opt (unify (sapply_eqs (Var (x := b)) xs)) (Var (x := b))" using x_free b_notvar by simp
      ultimately have "unify ((Var x, b) # xs) = scomp_opt (Some \<sigma>) (Var (x := b))" by auto
      then have "unify ((Var x, b) # xs) = Some (\<sigma> \<circ>s (Var (x := b)))" by simp
      then show ?thesis by simp
    qed
  qed
next
  case (3 v va x xs)
  assume 2: "\<exists>\<tau>. unifiess \<tau> ((Var x, Fun v va) # xs) \<Longrightarrow> \<exists>\<sigma>. unify ((Var x, Fun v va) # xs) = Some \<sigma>"
     and "\<exists>\<tau>. unifiess \<tau> ((Fun v va, Var x) # xs)"
  then obtain \<tau> where "unifiess \<tau> ((Fun v va, Var x) # xs)" by blast
  then have "unifiess \<tau> xs" "unifies \<tau> (Fun v va, Var x)" by (auto simp add: unifiess_def)
  then have "\<tau> \<cdot> (Var x) = \<tau> \<cdot> (Fun v va)" by (auto simp add: unifies.simps)
  then have "unifies \<tau> (Var x, Fun v va)" by (auto simp add: unifies.intros)
  then have "unifiess \<tau> ((Var x, Fun v va) # xs)" using \<open>unifiess \<tau> xs\<close> by (auto simp add: unifiess_def)
  then have "\<exists>\<sigma>. unify ((Var x, Fun v va) # xs) = Some \<sigma>" using 2 by blast
  moreover have "unify ((Fun v va, Var x) # xs) = unify ((Var x, Fun v va) # xs)" by simp
  ultimately show ?case by simp
next
  case (4 f l1 g l2 xs)
  then have 5: "f = g" "length l1 = length l2" "\<exists>\<tau>. unifiess \<tau> (xs @ zip l1 l2)" by (auto simp add: ex_unifier_fun)
  then have "\<exists>\<sigma>. unify (xs @ zip l1 l2) = Some \<sigma>" using 4 by simp
  then obtain \<sigma> where 6: "unify (xs @ zip l1 l2) = Some \<sigma>" by blast
  have "unify ((Fun f l1, Fun g l2) # xs) = unify (xs @ (zip l1 l2))" using 5 by simp
  then have "unify ((Fun f l1, Fun g l2) # xs) = Some \<sigma>" using 6 by simp 
  then show ?case by blast
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


(********* LEMMA 3 ************* LEMMA 3 ************ LEMMA 3 *************)

lemma three_one:   
  fixes \<sigma> :: "('f, 'v) subst" 
    and l :: "('f, 'v) equations"
  assumes "unify l = Some \<sigma>"
  shows "fv_eqs (sapply_eqs \<sigma> l) \<subseteq> fv_eqs l \<and> sdom \<sigma> \<subseteq> fv_eqs l \<and> svran \<sigma> \<subseteq> fv_eqs l"
using assms proof (induction l arbitrary: \<sigma> rule: unify.induct[case_names empty Var flip Fun]) 
  case empty print_cases
  assume "unify [] = Some \<sigma>" 
  then have "\<sigma> = Var" using \<open>unify [] = Some \<sigma>\<close> by simp
  then show ?case by auto
next
  case (Var x b xs)
  assume unif: "unify ((Var x, b) # xs) = Some \<sigma>"
  show ?case
  proof (cases "b = Var x")
      case b_var: True
      have f0: "unify xs = Some \<sigma>" using Var \<open>b = Var x\<close> unif by simp
      then have f1: "fv_eqs (sapply_eqs \<sigma> xs) \<subseteq> fv_eqs xs" using \<open>b = Var x\<close> Var by simp
      then have f2: "svran \<sigma> \<subseteq> fv_eqs xs" using \<open>b = Var x\<close> Var f0 by simp
      have "fv_eqs ((Var x, b) # xs) = fv_eqs xs \<union> {x}" using \<open>b = Var x\<close> by simp
      then have f3: "fv_eqs (sapply_eqs \<sigma> ((Var x, b) # xs)) = fv (\<sigma> x) \<union> fv_eqs (sapply_eqs \<sigma> xs)" using \<open>b = Var x\<close> by simp
      have "(fv (Var x) - sdom \<sigma>) \<subseteq> {x}" by auto
      moreover have "fv (\<sigma> x) \<subseteq> fv (Var x) - sdom \<sigma> \<union> svran \<sigma>" using  fv_sapply_sdom_svran
        by (metis UnCI calculation fv.simps(1) insert_Diff_if insert_not_empty sdom_intro subsetI subset_singletonD svran_intro)
      ultimately have "fv (\<sigma> x) \<subseteq> {x} \<union> fv_eqs xs" using f2 by auto
      then have "fv_eqs (sapply_eqs \<sigma> ((Var x, b) # xs)) \<subseteq> {x} \<union> fv_eqs xs \<union> fv_eqs xs" using f3 f1 Var by auto
      then show ?thesis using f0 Var \<open>b = Var x\<close> by auto
    next
      case False
      then have x_notfree: "x \<notin> fv b" using Var \<open>b \<noteq> Var x\<close> unify_notin by auto
      have 4: "fv_eqs ((Var x, b) # xs) = {x} \<union> fv_eqs xs \<union> fv b" by auto
      have 1: "scomp_opt (unify (sapply_eqs (Var(x := b)) xs)) (Var (x := b)) = Some \<sigma>" using Var \<open>b \<noteq> Var x\<close> \<open>x \<notin> fv b\<close> by auto
      then obtain \<sigma>\<^sub>2 where 2: "unify (sapply_eqs (Var(x := b)) xs) = Some \<sigma>\<^sub>2" using scomp_some by blast
      then have IH1: "fv_eqs (sapply_eqs \<sigma>\<^sub>2 (sapply_eqs (Var(x := b)) xs)) \<subseteq> fv_eqs (sapply_eqs (Var(x := b)) xs)"
        and IH2: "sdom \<sigma>\<^sub>2 \<subseteq> fv_eqs (sapply_eqs (Var(x := b)) xs)"
        and IH3: "svran \<sigma>\<^sub>2 \<subseteq> fv_eqs (sapply_eqs (Var(x := b)) xs)" using Var \<open>b \<noteq> Var x\<close> \<open>x \<notin> fv b\<close> by auto
      then have a1: "fv_eqs (sapply_eqs \<sigma>\<^sub>2 (sapply_eqs (Var(x := b)) xs)) \<subseteq> fv b \<union> fv_eqs xs"
        and a2: "sdom \<sigma>\<^sub>2 \<subseteq> fv b \<union> fv_eqs xs" 
        and a3: "svran \<sigma>\<^sub>2 \<subseteq> fv b \<union> fv_eqs xs" using fv_sapply_var False by (metis (mono_tags, lifting) Un_subset_iff fv.simps(1) singletonI sup.absorb_iff2)+
      let ?\<sigma>' = "\<sigma>\<^sub>2 \<circ>s (Var (x := b))"
      have 3: "\<sigma> = ?\<sigma>'" using 1 2 by simp
      have f1: "sdom \<sigma> \<subseteq> sdom \<sigma>\<^sub>2 \<union> {x}" using \<open>\<sigma> = \<sigma>\<^sub>2 \<circ>s Var(x := b)\<close> by fastforce
      have f2: "svran \<sigma> \<subseteq> svran \<sigma>\<^sub>2 \<union> fv b" by (metis False \<open>\<sigma> = \<sigma>\<^sub>2 \<circ>s Var(x := b)\<close> fv.simps(1) singletonI svran_scomp svran_single_non_trivial)
      have "fv_eqs (sapply_eqs \<sigma> ((Var x, b) # xs)) = fv_eqs (sapply_eqs ?\<sigma>' ((Var x, b) # xs))" using 3 by simp
      also have "... = fv (\<sigma>\<^sub>2 \<cdot> b) \<union> fv_eqs (sapply_eqs \<sigma>\<^sub>2 (sapply_eqs (Var (x := b)) xs))" by (auto simp add: x_notfree sapply_notin_fv)
      moreover have "fv (\<sigma>\<^sub>2 \<cdot> b) \<subseteq> fv b - sdom \<sigma>\<^sub>2 \<union> svran \<sigma>\<^sub>2" using fv_sapply_sdom_svran by fastforce
      ultimately have "fv_eqs (sapply_eqs \<sigma> ((Var x, b) # xs)) \<subseteq> fv_eqs ((Var x, b) # xs)" using 4 a1 a3 fv_sapply_sdom_svran by auto
      moreover have "sdom \<sigma> \<subseteq> fv_eqs ((Var x, b) # xs)" " svran \<sigma> \<subseteq> fv_eqs ((Var x, b) # xs)" using a2 a3 f1 f2 by auto
      ultimately show ?thesis by blast
    qed
  next 
  case (flip v va x xs)
  assume "unify ((Fun v va, Var x) # xs) = Some \<sigma>"
  then have "unify ((Var x, Fun v va) # xs) = Some \<sigma>" by simp 
  moreover have "fv_eqs (sapply_eqs \<sigma> ((Fun v va, Var x) # xs)) = fv_eqs (sapply_eqs \<sigma> ((Var x, Fun v va) # xs))" by (auto) 
  moreover have "fv_eqs ((Fun v va, Var x) # xs) = fv_eqs ((Var x, Fun v va) # xs)" by auto
  ultimately show ?case using flip by auto
next
  case (Fun f l1 g l2 xs)
  assume "unify ((Fun f l1, Fun g l2) # xs) = Some \<sigma>" 
  then have "f = g" "length l1 = length l2" "unify (xs @ zip l1 l2) = Some \<sigma>" using ex_unifier_fun unify_complete 
    by (metis option.distinct(1) unify.simps(4))+
  moreover have "fv_eqs (sapply_eqs \<sigma> ((Fun f l1, Fun g l2) # xs)) = fv_eqs (sapply_eqs \<sigma> (xs @ zip l1 l2))" using fv_eqs_zip[OF \<open>length l1 = length l2\<close>] fv_sapply_eqs fv_sapply_eq
    by (metis fv.simps(2) fv_eq.simps fv_eqs_cons fv_eqs_subst_eqs sapply_eqs.simps)
  moreover have "fv_eqs ((Fun f l1, Fun g l2) # xs) = fv_eqs (xs @ zip l1 l2)" using fv_eqs_zip[OF \<open>length l1 = length l2\<close>] by simp
  ultimately show ?case using Fun by auto
qed


lemma 3:
  fixes \<sigma> :: "('f, 'v) subst" 
    and l :: "('f, 'v) equations"
  assumes 1: "unify l = Some \<sigma>"
  shows subst_subs: "fv_eqs (sapply_eqs \<sigma> l) \<subseteq> fv_eqs l"
    and sdom_fv: "sdom \<sigma> \<subseteq> fv_eqs l"
    and svran_fv: "svran \<sigma> \<subseteq> fv_eqs l"
    and sdom_svran_disj: "sdom \<sigma> \<inter> svran \<sigma> = {}"
proof -
  show "fv_eqs (sapply_eqs \<sigma> l) \<subseteq> fv_eqs l" "sdom \<sigma> \<subseteq> fv_eqs l" "svran \<sigma> \<subseteq> fv_eqs l" using three_one[OF assms] by auto
next
  show "sdom \<sigma> \<inter> svran \<sigma> = {}"
  using assms proof (induction l arbitrary: \<sigma> rule: unify.induct)
    case 1
    then have "\<sigma> = Var" using assms by simp
    then show "sdom \<sigma> \<inter> svran \<sigma> = {}" by simp
  next
    case (2 x b xs)print_cases
    then show ?case
    proof (cases "b = Var x")
      case True
      then have "unify xs = Some \<sigma>" using 2 by simp
      then show ?thesis using 2 \<open>b = Var x\<close> by simp
    next
      case False
      then have "x \<notin> fv b" using 2 \<open>b \<noteq> Var x\<close> unify_notin by auto
      obtain \<sigma>\<^sub>2 where 3: "unify (sapply_eqs (Var(x := b)) xs) = Some \<sigma>\<^sub>2" using "2.prems" scomp_some False \<open>x \<notin> fv b\<close> by fastforce
      then have 4: "\<sigma> = \<sigma>\<^sub>2 \<circ>s (Var (x := b))" using 2 False \<open>x \<notin> fv b\<close> by (simp add: \<open>\<And>\<sigma>. \<lbrakk>b = Var x; unify xs = Some \<sigma>\<rbrakk> \<Longrightarrow> sdom \<sigma> \<inter> svran \<sigma> = {}\<close>)
      then have "sdom \<sigma>\<^sub>2 \<inter> svran \<sigma>\<^sub>2 = {}" using "2.IH" False \<open>x \<notin> fv b\<close> 3 by simp
      have "svran \<sigma>\<^sub>2 \<subseteq> fv_eqs (sapply_eqs (Var (x := b)) ((Var x, b) # xs))" using three_one[of "sapply_eqs (Var(x := b)) xs" "\<sigma>\<^sub>2"] 3 by auto
      moreover have "x \<notin> fv_eqs (sapply_eqs (Var (x := b)) ((Var x, b) # xs))" by (metis Diff_iff False UnE \<open>x \<notin> fv b\<close> fv_sapply_eqs_sdom_svran sdom_single_non_trivial singletonI svran_single_non_trivial)
      ultimately have "x \<notin> svran \<sigma>\<^sub>2" by blast
      show ?thesis
      proof (rule Int_emptyI)
        fix y
        assume 6: "y \<in> sdom \<sigma>" "y \<in> svran \<sigma>"
        have "sdom \<sigma> \<subseteq> sdom \<sigma>\<^sub>2 \<union> sdom (Var (x := b))" using 4 by (auto simp add: sdom_def)
        then have "y \<in> sdom \<sigma>\<^sub>2 \<union> {x}" using 6 \<open>b \<noteq> Var x\<close> sdom_single_non_trivial by auto
        have "svran \<sigma> \<subseteq> svran \<sigma>\<^sub>2 \<union> svran (Var (x := b))" using 4 by (simp add: svran_scomp)
        then have "y \<in> svran \<sigma>\<^sub>2 \<union> fv b" using 6 \<open>b \<noteq> Var x\<close> svran_single_non_trivial by auto
        then have "y \<noteq> x" using \<open>x \<notin> svran \<sigma>\<^sub>2\<close> \<open>x \<notin> fv b\<close> by blast
        then have "y \<in> sdom \<sigma>\<^sub>2" using \<open>y \<in> sdom \<sigma>\<^sub>2 \<union> {x}\<close> by blast
        obtain z where 7: "z \<in> sdom \<sigma> \<and> y \<in> fv(\<sigma> z)" using 6 by auto 
        then show "False" 
        proof (cases "z = x")
          case True
          then have "\<sigma> z = \<sigma>\<^sub>2 \<cdot> t" using 4 \<open>sdom \<sigma>\<^sub>2 \<inter> svran \<sigma>\<^sub>2 = {}\<close> \<open>y \<in> sdom \<sigma>\<^sub>2\<close> \<open>z \<in> sdom \<sigma> \<and> y \<in> fv (\<sigma> z)\<close> fv_sapply_sdom_svran by fastforce 
          then have "y \<in> fv(\<sigma>\<^sub>2 \<cdot> t)" using 7 by auto
          then have "y \<in> fv t - sdom \<sigma>\<^sub>2 \<union> svran \<sigma>\<^sub>2" using fv_sapply_sdom_svran by fastforce
          then have "y \<in> svran \<sigma>\<^sub>2" using \<open>y \<in> sdom \<sigma>\<^sub>2\<close> by blast
          then show ?thesis using \<open>y \<in> sdom \<sigma>\<^sub>2\<close> \<open>sdom \<sigma>\<^sub>2 \<inter> svran \<sigma>\<^sub>2 = {}\<close> by blast
        next
          case False
          then have "\<sigma> z = \<sigma>\<^sub>2 z" using 4 by simp
          then have "z \<in> sdom \<sigma>\<^sub>2" using 7 by fastforce
          then have "y \<in> svran \<sigma>\<^sub>2" using 7  \<open>\<sigma> z = \<sigma>\<^sub>2 z\<close> by auto
          then show ?thesis using \<open>y \<in> sdom \<sigma>\<^sub>2\<close> \<open>sdom \<sigma>\<^sub>2 \<inter> svran \<sigma>\<^sub>2 = {}\<close> by blast
        qed
      qed
    qed
  next
    case (3 v va x xs) print_cases
    then have "unify ((Var x, Fun v va) # xs) = Some \<sigma>" by simp
    then show ?case using "3.IH" by simp 
  next
    case (4 f l1 g l2 xs) print_cases
    then have "unifiess \<sigma> ((Fun f l1, Fun g l2) # xs)" by (simp add: unify_return)
    then have 5: "g = f" "length l1 = length l2" using ex_unifier_fun by fastforce+
    then have "unify (xs @ zip l1 l2) = Some \<sigma>" using "4.prems" by simp 
    then show ?case using "4.IH" 5 assms by auto
  qed
qed


(****************************** ( 4A ) ***************************)
inductive wf_term :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  for arity :: "'f \<Rightarrow> nat"
  where
  wf_term_intro_var:"wf_term arity (Var _)"
| wf_term_intro_fun:"(length l = arity f) \<Longrightarrow> \<forall> x \<in> set l. wf_term arity x \<Longrightarrow> wf_term arity (Fun f l)"

inductive wf_subst :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) subst \<Rightarrow> bool"
  for arity :: "'f \<Rightarrow> nat" where
  "\<lbrakk> \<forall>x. wf_term arity (\<sigma> x) \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"

lemma wf_subst_var: "\<lbrakk> wf_term arity t; x \<notin> fv t \<rbrakk> \<Longrightarrow> wf_subst arity (Var (x := t))"
  by (auto simp add: wf_subst.simps wf_term.intros)

inductive wf_eq :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equation \<Rightarrow> bool" where
  "\<lbrakk> wf_term arity a; wf_term arity b \<rbrakk> \<Longrightarrow> wf_eq arity (a,b)"

lemma wf_eqE: "wf_eq arity (a, b) \<Longrightarrow> (wf_term arity a \<Longrightarrow> wf_term arity b \<Longrightarrow> P) \<Longrightarrow> P"
  using wf_eq.cases by auto

inductive wf_eqs :: "('f \<Rightarrow> nat) \<Rightarrow> ('f, 'v) equations \<Rightarrow> bool" where
  "\<lbrakk> \<forall>x \<in> set l. wf_eq arity x \<rbrakk> \<Longrightarrow> wf_eqs arity l" 


(********************************** ( 4B )  **********************************)
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

lemma wf_eqs_sapply_eqs: "\<lbrakk> wf_eqs arity eqs; wf_subst arity \<sigma> \<rbrakk> \<Longrightarrow> wf_eqs arity (sapply_eqs \<sigma> eqs)"
  apply (induction eqs)
  by (simp_all add: wf_eq_sapply_eq wf_eqs.simps)

lemma wf_subst_scomp: "\<lbrakk> wf_subst arity \<sigma>; wf_subst arity \<tau> \<rbrakk> \<Longrightarrow> wf_subst arity (\<sigma> \<circ>s \<tau>)"
  by (simp add: wf_subst.simps wf_term_sapply)


lemma wf_subst_unify: "\<lbrakk> unify l = Some \<sigma>; wf_eqs arity l \<rbrakk> \<Longrightarrow> wf_subst arity \<sigma>"
proof (induction l arbitrary: \<sigma> rule: unify.induct)
  case 1
  then show ?case by (auto intro: wf_term.intros wf_subst.intros)
next
case (2 x b xs)
  then show ?case
  proof (cases "b = Var x")
    case True
    then have "unify xs = Some \<sigma>" using 2 by simp
    moreover have "wf_eqs arity xs" using 2 by (simp add: wf_eqs.simps)
    ultimately show ?thesis using \<open>b = Var x\<close> 2 by simp
  next
    case False
    then show ?thesis 
    proof (cases "x \<in> fv b")
      case True
      then have "unify ((Var x, b) # xs) = None" using \<open>b \<noteq> Var x\<close> by simp
      moreover have "unify ((Var x, b) # xs) = Some \<sigma>" using 2 by simp
      ultimately have False by simp
      then show ?thesis by simp
    next
      case False
      let ?term = "sapply_eqs (Var(x := b)) xs"
      have "unify ((Var x, b) # xs) = scomp_opt (unify ?term) (Var (x := b))" using \<open>x \<notin> fv b\<close> \<open>b \<noteq> Var x\<close> by simp
      then have 3: "scomp_opt (unify ?term) (Var (x := b)) = Some \<sigma>" using 2 by simp 
      then have "\<exists>\<tau>. unify ?term = Some \<tau>" by (auto simp add: scomp_some)
      then obtain \<sigma>\<^sub>2 where 4: "unify ?term = Some \<sigma>\<^sub>2" by blast
      have "wf_term arity b" using 2 by (simp add: wf_term.intros wf_eqs.simps wf_eq.simps)
      then have "wf_subst arity (Var (x := b))" using \<open>x \<notin> fv b\<close> by (simp add: wf_subst_var)
      moreover have "wf_eqs arity xs" using 2 by (simp add: wf_eqs.simps)
      ultimately have "wf_eqs arity ?term" using wf_eqs_sapply_eqs by simp 
      then show ?thesis using \<open>b \<noteq> Var x\<close> \<open>x \<notin> fv b\<close> 2 4 \<open>wf_subst arity (Var(x := b))\<close> wf_subst_scomp by fastforce
    qed
  qed
next
  case (3 v va x xs)
  have "wf_eqs arity ((Var x, Fun v va) # xs)" using 3 wf_eqs.intros wf_eq.intros wf_term.intros by (metis insert_iff list.set(2) wf_eqE wf_eqs.cases)
  moreover have "unify ((Var x, Fun v va) # xs) = Some \<sigma>" using 3 by simp
  ultimately show ?case using 3 by simp
next
  case (4 f l1 g l2 xs)
  then have 5: "f = g" "length l1 = length l2" "unify (xs @ zip l1 l2) = Some \<sigma>" by (simp_all split: if_splits)
  have "wf_eq arity (Fun f l1, Fun g l2)" using 4 by (simp add: wf_eqs.simps)
  then have "\<forall>x\<in>set l1. wf_term arity x" "\<forall>x\<in>set l2. wf_term arity x" using wf_term.simps by (metis term.distinct(1) term.inject(2) wf_eqE)+
  then have "wf_eqs arity (zip l1 l2)" using wf_eqs.intros by (simp add: \<open>\<And>l arity. \<forall>x\<in>set l. wf_eq arity x \<Longrightarrow> wf_eqs arity l\<close> set_zip set_zip_leftD set_zip_rightD wf_eq.simps)
  moreover have "wf_eqs arity (xs)" using 4 by (simp add: wf_eqs.simps)
  ultimately have "wf_eqs arity (xs @ zip l1 l2)" by (metis Un_iff set_append wf_eqs.simps)
  then show ?case using 4 5 by simp
qed
end

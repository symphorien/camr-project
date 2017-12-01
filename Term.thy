chapter {* camr project *}

theory Term imports Main Unification begin
(* assignment 5 *)
(* (a) *)

(* definition of messages *)
type_synonym var = string
type_synonym const = string
datatype msg =
Hash msg | Concat msg msg | Sym_encrypt msg msg | Pub_encrypt msg msg | Sign msg msg
| Const const | Variable var
(* Pub_encrypt content key  and so on*)

(* (b) *)
(* embedding *)
datatype symbol =
SHash | SConcat | SSym_encrypt | SPub_encrypt | SSign | SConst const
fun arity :: "symbol \<Rightarrow> nat" where
"arity SHash = 1"
| "arity SConcat = 2"
| "arity SSym_encrypt = 2"
| "arity SPub_encrypt = 2"
| "arity SSign = 2"
| "arity (SConst _) = 0"

(* (c) *)
type_synonym msg_term = "(symbol, var) term"

fun embed :: "msg \<Rightarrow> msg_term" where
"embed (Hash x) = Fun SHash [embed x]"
| "embed (Concat x y) = Fun SConcat [embed x, embed y]"
| "embed (Sym_encrypt x y) = Fun SSym_encrypt [embed x, embed y]"
| "embed (Pub_encrypt x y) = Fun SPub_encrypt [embed x, embed y]"
| "embed (Sign x y) = Fun SSign [embed x, embed y]"
| "embed (Const x) = Fun (SConst x) []"
| "embed (Variable x) = Var x"

fun msg_of_term :: "msg_term \<Rightarrow> msg" where
"msg_of_term (Fun SHash [x]) = Hash (msg_of_term x)"
| "msg_of_term (Fun SConcat [x, y]) = Concat (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun SSym_encrypt [x, y]) = Sym_encrypt (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun SPub_encrypt [x, y]) = Pub_encrypt (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun SSign [x, y]) = Sign (msg_of_term x) (msg_of_term y)"
| "msg_of_term (Fun (SConst x) []) = Const x"
| "msg_of_term (Var x) = Variable x"

(* embedding lemmas *)
lemma wf_term_embed [simp]: "wf_term arity (embed msg)"
proof(induction msg)
qed(auto intro:wf_term.intros)

lemma msg_of_term_embed [simp]: "msg_of_term (embed x) = x"
proof(induction x)
qed auto

lemma embed_msg_of_term [simp]: "wf_term arity x \<Longrightarrow> embed (msg_of_term x) = x"
proof(induction rule:wf_term.induct)
case (wf_term_intro_var uu)
then show ?case by auto
next
case (wf_term_intro_fun l f)
  then show ?case
(* arity goes up to 2 so pattern match on up to 2 elements of l*)
  proof(cases f;cases l;(cases "tl l")?)
  qed(auto simp add:"wf_term_intro_fun.IH")
qed

(* (c) : transfer of various functions via embedding 
   naming convention: ${fn} \<rightarrow> ${fn}_msg_*)
(* fv *)
definition fv_msg:: "msg \<Rightarrow> var set" where
"fv_msg m = fv (embed m)"

(* substs *)
type_synonym subst_msg = "var \<Rightarrow> msg"
definition embed_subst :: "subst_msg \<Rightarrow> (var \<Rightarrow> msg_term)" where
"embed_subst s = embed o s"
definition subst_from_embed :: "(var \<Rightarrow> msg_term) \<Rightarrow> subst_msg"  where
"subst_from_embed s = msg_of_term o s"

lemma embed_subst_from_embed [simp]: "wf_subst arity x \<Longrightarrow> embed_subst (subst_from_embed x) = x"
proof(induction rule:wf_subst.induct)
  case (1 \<sigma>)
  then show ?case by(auto simp add:fun_eq_iff embed_subst_def subst_from_embed_def)
qed

lemma wf_subst_embed_subst[simp]: "wf_subst arity (embed_subst s)"
  by(auto intro!:wf_subst.intros simp add:embed_subst_def)

lemma wf_term_embed_subst[simp]: "wf_term arity (embed_subst s x)"
  by(auto simp add:embed_subst_def intro:wf_term.intros)

lemma subst_from_embed_embed_subst[simp]:"subst_from_embed (embed_subst s) = s"
  by(auto simp add:embed_subst_def subst_from_embed_def)

lemma embed_subst_Variable[simp]:"embed_subst Variable = Var"
  by(auto simp add:embed_subst_def)

lemma subst_from_embed_Var[simp]:"subst_from_embed Var = Variable"
  by(auto simp add:subst_from_embed_def)

(* sapply *)
definition sapply_msg :: "subst_msg \<Rightarrow> msg \<Rightarrow> msg" where
"sapply_msg s m = msg_of_term (sapply (embed_subst s) (embed m))"

lemma sapply_msg_simps:
"sapply_msg s (Hash x) = Hash (sapply_msg s x)"
"sapply_msg s (Concat x y) = Concat (sapply_msg s x) (sapply_msg s y)"
"sapply_msg s (Sym_encrypt x y) = Sym_encrypt (sapply_msg s x) (sapply_msg s y)"
"sapply_msg s (Pub_encrypt x y) = Pub_encrypt (sapply_msg s x) (sapply_msg s y)"
"sapply_msg s (Sign x y) = Sign (sapply_msg s x) (sapply_msg s y)"
"sapply_msg s (Const z) = Const z"
"sapply_msg Variable x = x"
  by(auto simp add:sapply_msg_def)

(* scomp *)
definition scomp_msg:: "subst_msg \<Rightarrow> subst_msg \<Rightarrow> subst_msg" where
"scomp_msg s t = subst_from_embed ((embed_subst s) \<circ>s (embed_subst t))"

lemma embed_scomp_wf: "wf_subst arity ((embed_subst t) \<circ>s (embed_subst s))"
  by(simp add:wf_subst_scomp)

lemma sapply_msg_scomp_msg:
"sapply_msg (scomp_msg t s) c = sapply_msg t (sapply_msg s c)" (is "?lhs = ?rhs")
  by(auto simp add:sapply_msg_def scomp_msg_def embed_scomp_wf wf_term_sapply)

lemma scomp_variable[simp]: "scomp_msg Variable s = s" "scomp_msg s Variable = s"
  by(simp_all add:scomp_msg_def)

lemma scomp_msg_assoc: "scomp_msg (scomp_msg a b) c = scomp_msg a (scomp_msg b c)" (is "?lhs = ?rhs")
  by(simp_all add:scomp_msg_def embed_scomp_wf scomp_assoc)

(* equations *)
type_synonym eq_msg = "msg \<times> msg"
fun embed_eq :: "eq_msg \<Rightarrow> (symbol, var) equation" where
"embed_eq (a, b) = (embed a, embed b)"
fun eq_from_embed:: "(symbol, var) equation \<Rightarrow> eq_msg" where
"eq_from_embed (a, b) = (msg_of_term a, msg_of_term b)"

lemma wf_embed_eq [simp]:"wf_eq arity (embed_eq e)" by(cases e; auto intro:wf_eq.intros)
lemma wf_embed_eqs [simp]:"wf_eqs arity (map embed_eq l)"
proof(rule wf_eqs.intros)
qed simp
lemma "embed_eq_eq_from_embed" [simp]: "wf_eq arity e \<Longrightarrow> embed_eq (eq_from_embed e) = e"
proof(cases e)
  case (Pair a b)
  assume "wf_eq arity e"
  then have x:"wf_eq arity (a, b)" by(simp add:Pair)
  then have "wf_term arity a" by(cases rule:wf_eq.cases; auto)
  moreover from x have "wf_term arity b" by(cases rule:wf_eq.cases; auto)
  ultimately show "embed_eq (eq_from_embed e) = e"
    by(auto simp add:Pair)
qed
lemma "eq_from_embed_embed_eq" [simp]: "eq_from_embed (embed_eq e) = e"
  by(cases e;auto)

(* unifies *)
definition unifies_msg :: "subst_msg \<Rightarrow> eq_msg \<Rightarrow> bool" where
  "unifies_msg s eq = unifies (embed_subst s) (embed_eq eq)"

(* unifiess *)
definition unifiess_msg :: "subst_msg \<Rightarrow> eq_msg list \<Rightarrow> bool" where
  "unifiess_msg s eqs = unifiess (embed_subst s) (map embed_eq eqs)"

lemma unifiess_msgE: "unifiess_msg s eqs \<Longrightarrow> ((\<And> eq. eq \<in> set eqs \<Longrightarrow> unifies_msg s eq) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add:unifies_msg_def unifiess_msg_def unifiess_def)

lemma unifies_msgE: "unifies_msg s (a, b) \<Longrightarrow> (sapply_msg s a = sapply_msg s b \<Longrightarrow> P) \<Longrightarrow> P"
  apply(simp add:unifies_msg_def)
  apply(cases rule:unifies.cases)
   apply(auto simp add:sapply_msg_def)
  done

(* unify *)
fun bind:: "('a\<Rightarrow>'b) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
"bind f x = (case x of None \<Rightarrow> None | (Some x) \<Rightarrow> Some (f x))"

definition unify_msg :: "eq_msg list \<Rightarrow> subst_msg option" where
"unify_msg eqs = bind subst_from_embed (unify (map embed_eq eqs))"


(* (e) *)
lemma unify_msg_return: "unify_msg l = Some \<sigma> \<Longrightarrow> unifiess_msg \<sigma> l"
proof -
  let ?s="map embed_eq l"
  assume returns:"unify_msg l = Some \<sigma>"
(* first we need to show that x is well formed *)
  then obtain x where xdef:"unify ?s = Some x" and sigmadef:"\<sigma> = subst_from_embed x"
    by(auto simp add:unify_msg_def unifiess_msg_def split:option.split_asm)
  have "wf_eqs arity ?s" 
    by(auto intro!:wf_eqs.intros wf_eq.intros)
  from xdef and this have "wf_subst arity x" by(rule wf_subst_unify)
(* now we can use the embedding easily *)
  show ?thesis
    apply(auto simp add:unify_msg_def xdef sigmadef unifiess_msg_def)
    apply(rule unify_return)
  apply(simp only:xdef `wf_subst arity x` embed_subst_from_embed)
    done
qed

(* (f) *)
fun fv_eq_msg:: "eq_msg \<Rightarrow> var set" where
"fv_eq_msg (a, b) = fv_msg a \<union> fv_msg b"
definition fv_eqs_msg:: "eq_msg list \<Rightarrow> var set" where
"fv_eqs_msg l = fv_eqs (map embed_eq l)"

lemma fv_eqs_msg_fv_msg: "fv_eqs_msg l = (\<Union> x \<in> set l. fv_eq_msg x)"
  by(auto simp add:fv_eqs_msg_def fv_msg_def)

fun sapply_eq_msg:: "subst_msg \<Rightarrow> eq_msg \<Rightarrow> eq_msg" where
"sapply_eq_msg s (a, b) = (sapply_msg s a, sapply_msg s b)"
definition sapply_eqs_msg:: "subst_msg \<Rightarrow> eq_msg list \<Rightarrow> eq_msg list" where
"sapply_eqs_msg s l = map eq_from_embed (sapply_eqs (embed_subst s) (map embed_eq l))"

lemma "sapply_eqs_msg s l = map (sapply_eq_msg s) l"
  by(auto simp add:sapply_eqs_msg_def sapply_msg_def)

definition sdom_msg:: "subst_msg \<Rightarrow> var set" where
"sdom_msg s = sdom (embed_subst s)"
definition sran_msg:: "subst_msg \<Rightarrow> msg set" where
"sran_msg s = image msg_of_term (sran (embed_subst s))"
definition svran_msg:: "subst_msg \<Rightarrow> var set" where
"svran_msg s = svran (embed_subst s)"

lemma sdom_msgI: "s x \<noteq> Variable x \<Longrightarrow> x \<in> sdom_msg s"
    by(cases "s x")(auto simp add:sdom_msg_def sdom_def embed_subst_def embed_def)
lemma sdom_msg_def_real: "sdom_msg s = {x.  s x \<noteq> Variable x}"
proof(rule equalityI)
  show "sdom_msg s \<subseteq> {x. s x \<noteq> Variable x}"
    by(auto simp add:sdom_msg_def sdom_def embed_subst_def embed_def intro:sdom_msgI)
next
  show "{x. s x \<noteq> Variable x} \<subseteq> sdom_msg s"
    by(auto intro:sdom_msgI)
qed

lemma embed_neg_inj:"embed x \<noteq> embed y \<Longrightarrow> x \<noteq> y"
  by(auto)

lemma sran_msg_def_real:  "sran_msg s = {s x | x. x \<in> sdom_msg s}"
proof(rule equalityI;rule subsetI)
  fix x
  assume "x \<in> sran_msg s"
  then obtain v where dom:"v\<in>sdom_msg s" and xdef:"embed x = (embed_subst s) v" by(auto simp add:sran_def sdom_msg_def sran_msg_def)

  from xdef have "msg_of_term (embed x)=msg_of_term ((embed_subst s) v)" by(simp)
  then have "x=s v" by(simp add:embed_subst_def)

  from this and dom show "x \<in> {s x |x. x \<in> sdom_msg s}" by(auto)
next
  fix t
  assume "t \<in> {s x |x. x \<in> sdom_msg s}"
  then obtain x where tdef:"t=s x" and dom:"x \<in> sdom_msg s" by(auto)
  from dom have "x \<in> sdom (embed_subst s)" by(simp add: sdom_msg_def)
  moreover from tdef have "t = msg_of_term ((embed_subst s) x)" by(simp add:embed_subst_def)
  ultimately show "t \<in> sran_msg s"
    by(auto simp add:sran_msg_def sran_def)
qed

lemma wf_term_sran[simp]:"wf_subst arity s \<Longrightarrow> x\<in>sran s \<Longrightarrow> wf_term arity x"
  by(auto simp add:sran_def wf_subst.simps)

lemma svran_msg_def_real: "svran_msg s = (\<Union> t \<in> sran_msg s. fv_msg t)"
proof(rule equalityI;rule subsetI)
  fix x
  assume "x \<in> svran_msg s"
  then obtain t where xdef:"x \<in> fv t" and tdef:"t \<in> sran (embed_subst s)"by(auto simp add:svran_msg_def svran_def)
  have "wf_subst arity (embed_subst s)" by simp
  from this and tdef have "wf_term arity t" by(rule wf_term_sran)
  from this and xdef and tdef have "x \<in> fv_msg (msg_of_term t)" and "msg_of_term t \<in> sran_msg s"
    by(auto simp add:sran_msg_def fv_msg_def)
  then show "x \<in> (\<Union> t \<in> sran_msg s. fv_msg t)" by auto
next
  fix x
  assume "x\<in>(\<Union> t \<in> sran_msg s. fv_msg t)"
  then obtain t where tdef:"t\<in> (sran_msg s)" and xdef:"x \<in> fv(embed t)" by(auto simp add:fv_msg_def) 
  from tdef have "embed t \<in> sran (embed_subst s)" by(auto simp add:sran_msg_def sran_def)
  from this and xdef show "x \<in> svran_msg s" by(auto simp add:svran_msg_def svran_def)
qed

lemma sdom_msg_simp: "sdom_msg (Variable(x:=Const y)) = {x}" (is "sdom_msg ?s = _")
  by(auto simp add:sdom_msg_def_real)

lemma fv_sapply_sdom_svran_msg: "fv_msg (sapply_msg s t) \<subseteq> ((fv_msg t) - (sdom_msg s)) \<union> (svran_msg s)"
(is "?lhs \<subseteq> ?rhs")
proof(rule subsetI)
  fix x
  let ?s = "embed_subst s"
  let ?t = "embed t"
  assume "x \<in> fv_msg (sapply_msg s t)"
  then have "x \<in> fv (?s \<cdot> ?t)"
    by(simp add:sdom_msg_def sapply_msg_def svran_msg_def fv_msg_def wf_term_sapply)
  then have "x \<in> (fv (Term.embed t) - sdom (embed_subst s)) \<union> svran (embed_subst s)"
    by(rule fv_sapply_sdom_svran)
  then show "x \<in> ?rhs" 
    by(simp add:sdom_msg_def sapply_msg_def svran_msg_def fv_msg_def wf_term_sapply)
qed

lemma l3_msg:
  fixes \<sigma> :: "subst_msg" 
    and l :: "eq_msg list"
  assumes "unify_msg l = Some s"
  shows "fv_eqs_msg (sapply_eqs_msg s l) \<subseteq> fv_eqs_msg l"
    and "sdom_msg s \<subseteq> fv_eqs_msg l"
    and "svran_msg s \<subseteq> fv_eqs_msg l"
    and "sdom_msg s \<inter> svran_msg s = {}"
proof -
  let ?l' = "map embed_eq l"
  from assms obtain s'
    where return:"unify ?l' = Some s'" and sdef:"s = subst_from_embed s'"
    by(auto simp add:unify_msg_def sdom_msg_def split:option.split_asm)
  have wf:"wf_eqs arity ?l'" by simp
  from return  and this have wfs:"wf_subst arity s'" by(rule wf_subst_unify)

(* goal 1*)
  from return have "fv_eqs (sapply_eqs s' ?l') \<subseteq> fv_eqs ?l'" by(rule 3)
  then  show  "fv_eqs_msg (sapply_eqs_msg s l) \<subseteq> fv_eqs_msg l"
    by(simp add:sapply_eqs_msg_def wf_eq_sapply_eq fv_eqs_msg_def sdef wf wfs)
(*goal 2*)
  from return have "sdom s' \<subseteq> fv_eqs ?l'" by(rule 3)
  then show "sdom_msg s \<subseteq> fv_eqs_msg l"
    by(simp add:sdom_msg_def fv_eqs_msg_def sdef wfs)

(* goal 3*)
  from return have "svran s' \<subseteq> fv_eqs ?l'" by(rule 3)
  then show "svran_msg s \<subseteq> fv_eqs_msg l"
    by(simp add:svran_msg_def fv_eqs_msg_def sdef wfs)
      (*goal 4*)
  from return have "sdom s' \<inter> svran s' = {}" by(rule 3)
  then show "sdom_msg s \<inter> svran_msg s = {}"
    by(simp add:sdom_msg_def svran_msg_def fv_eqs_msg_def sdef wfs)
qed

end

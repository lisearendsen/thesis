theory syntaxsemantics
imports Main
begin

datatype 'a regularformula =
  eps | acts "'a set" |
  after "'a regularformula" "'a regularformula"| 
  union "'a regularformula" "'a regularformula" | 
  repeat "'a regularformula"

(* from "HOL-Library.Regular-Sets.Regular_Exp" *)
definition conc :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr \<open>@@\<close> 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

(*this is probably also defined already*)
lemma conclem : "a \<in> A \<and> b \<in> B \<Longrightarrow> a@b \<in> A@@B"
  using conc_def by fastforce

lemma conclem' : "(ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> a \<in> A \<and> b \<in> B)"
  by (simp add: conc_def)

overloading form_pow == "compow :: nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
begin
  primrec form_pow :: "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  "form_pow 0 A = {[]}" |
  "form_pow (Suc n) A = A @@ (form_pow n A)"
end

definition form_pow :: "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  form_pow [code_abbrev]: "form_pow = compow"

fun regformtolanguage :: "'a regularformula \<Rightarrow> 'a list set" where
"regformtolanguage eps = {[]}" |
"regformtolanguage (acts A) = {[a] |a. (a \<in>A)}" |
"regformtolanguage (after R Q) = ({r @ q |r q. (r \<in> regformtolanguage R) \<and> (q \<in> regformtolanguage Q)})" |
"regformtolanguage (union R Q) = (regformtolanguage R) \<union> (regformtolanguage Q)" |
"regformtolanguage (repeat R) = (\<Union>n. (regformtolanguage R) ^^ n)"

value "regformtolanguage (eps) :: nat list set" 
value "regformtolanguage (acts {}) :: nat list set" 
value "regformtolanguage (after (acts {1, 2}) (acts {3, 4})) :: nat list set" 

datatype 'a formula =
  tt | ff | var nat |
  neg "'a formula" |
  and' "'a formula" "'a formula" | 
  or "'a formula" "'a formula" | 
  box 'a "'a formula" |
  diamond 'a "'a formula" |
  nu "'a formula" |
  mu "'a formula"

value "diamond 2 (box 1 tt) :: nat formula"
value "nu (var 0) :: nat formula "

record ('a, 's) lts =
transition :: "('s * 'a * 's) set"
initial :: "'s set"

datatype example_states = s\<^sub>0 | s\<^sub>1
datatype example_actions = \<a> | \<b>

definition example_lts :: "(example_actions, example_states) lts" where
"example_lts \<equiv> \<lparr>transition = {(s\<^sub>0, \<b>, s\<^sub>1), (s\<^sub>1, \<a>, s\<^sub>0), (s\<^sub>1, \<a>, s\<^sub>1)}, initial = {s\<^sub>0}\<rparr>"

fun newenvironment :: "(nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's set) " where
"newenvironment e S 0 = S" |
"newenvironment e S (Suc n) = e n"

lemma newenvironmentsuccessorcomplement [simp] : 
"(newenvironment e S)((Suc i) := - ((newenvironment e S) (Suc i))) = newenvironment (e(i := - e i)) S"
proof
  fix n
  show "((newenvironment e S) (Suc i := - newenvironment e S (Suc i))) n = newenvironment (e(i := - e i)) S n"
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentzerocomplement [simp] : 
"(newenvironment e S)(0 := (-(newenvironment e S) 0)) = (newenvironment e (-S))"
proof
  fix n
  show "((newenvironment e S)(0 := ((-(newenvironment e S) 0)))) n  = (newenvironment e (-S)) n "
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentswitchsuccessor [simp] : 
"newenvironment (e(i :=  S')) S'' = (newenvironment e S'')((Suc i) := S')"
proof
  fix n
  show "(newenvironment (e(i :=  S')) S'') n = ((newenvironment e S'')((Suc i) := S')) n"
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentswitchzero [simp] : 
"(newenvironment e S'')(0 := S') = newenvironment e S'"
proof
  fix n
  show "((newenvironment e S'')(0 := S')) n = newenvironment e S' n"
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentshift [simp] : 
"X > 0 \<longrightarrow> (newenvironment e S') X = e (X - Suc 0)"
  apply (induct_tac X)
  apply (simp_all)
  done

fun formulasemantics :: "'a formula  \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set" (\<open>\<lbrakk>_\<rbrakk> _ _\<close> [80, 80, 80] 80) 
where 
  "\<lbrakk>tt\<rbrakk> M e = UNIV " |
  "\<lbrakk>ff\<rbrakk> M e =  {}" |
  "\<lbrakk>var X\<rbrakk> M e  = e X" |
  "\<lbrakk>neg f\<rbrakk> M e = -(\<lbrakk>f\<rbrakk> M e)" |
  "\<lbrakk>and' f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<inter> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>or f f'\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e \<union> \<lbrakk>f'\<rbrakk> M e" |
  "\<lbrakk>diamond act f\<rbrakk> M e = {s. \<exists> s'. (s, act, s') \<in> (transition M) \<and> s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>box act f\<rbrakk> M e = {s. \<forall> s'. (s, act, s') \<in> (transition M) \<longrightarrow>  s'\<in> \<lbrakk>f\<rbrakk> M e}" |
  "\<lbrakk>nu f\<rbrakk> M e = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" |
  "\<lbrakk>mu f\<rbrakk> M e = \<Inter> {S'. S' \<supseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}"

lemma "\<lbrakk>box \<a> ff\<rbrakk> example_lts e = {s\<^sub>0}"
  apply (simp add: example_lts_def)
  using example_states.exhaust apply auto
  done

lemma "\<lbrakk>nu (diamond \<a> (var 0))\<rbrakk> example_lts e = {s\<^sub>1}"
  apply (simp add: example_lts_def)
proof-
  have "\<forall>(S':: example_states set). S' \<subseteq> {s\<^sub>0, s\<^sub>1}" using example_states.exhaust by auto
  hence "(\<forall>(S':: example_states set). S' \<subseteq> {s. \<exists>s'. (s = s\<^sub>1 \<and> s' = s\<^sub>0 \<or> s = s\<^sub>1 \<and> s' = s\<^sub>1) \<and> s' \<in> S'} = (S' = {} \<or> S' = {s\<^sub>1}))" by auto
  thus "\<Union> {S'. S' \<subseteq> {s. \<exists>s'. (s = s\<^sub>1 \<and> s' = s\<^sub>0 \<or>  s = s\<^sub>1 \<and> s' = s\<^sub>1) \<and> s' \<in> S'}} = {s\<^sub>1}" by auto
qed

fun shiftup :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(shiftup tt i) = tt " |
  "(shiftup ff i) = ff" |
  "(shiftup (var X) i)  = (if X < i then var X else var (X + 1))" |
  "(shiftup (neg f) i) = neg (shiftup f i)" |
  "(shiftup (and' f f') i) = and' (shiftup f i) (shiftup f' i) " |
  "(shiftup (or f f') i) = or (shiftup f i) (shiftup f' i)" |
  "(shiftup (diamond act f) i) = diamond act (shiftup f i) " |
  "(shiftup (box act f) i) = box act (shiftup f i)" |
  "(shiftup (nu f) i) = nu (shiftup f (Suc i))" |
  "(shiftup (mu f) i) = mu (shiftup f (Suc i))"

fun shiftdown :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(shiftdown tt i) = tt " |
  "(shiftdown ff i) = ff" |
  "(shiftdown (var X) i)  = (if X \<le> i then var X else var (X - 1))" |
  "(shiftdown (neg f) i) = neg (shiftdown f i)" |
  "(shiftdown (and' f f') i) = and' (shiftdown f i) (shiftdown f' i) " |
  "(shiftdown (or f f') i) = or (shiftdown f i) (shiftdown f' i)" |
  "(shiftdown (diamond act f) i) = diamond act (shiftdown f i) " |
  "(shiftdown (box act f) i) = box act (shiftdown f i)" |
  "(shiftdown (nu f) i) = nu (shiftdown f (Suc i))" |
  "(shiftdown (mu f) i) = mu (shiftdown f (Suc i))"

lemma shiftupanddown : "shiftdown (shiftup f i) i = f"
  by (induct f arbitrary : i; simp)

definition shiftdownenv :: "(nat \<Rightarrow> 's set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's set) " where
"shiftdownenv e i n = (if n < i then e n else e (n + 1))"

fun Diamondlist :: "'a list \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where
"Diamondlist [] f = ff" |
"Diamondlist (a # as) f = or (diamond a f) (Diamondlist as f)"

fun Diamond :: "'a regularformula \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where 
"Diamond eps f = f" |
"Diamond (acts A) f = Diamondlist (if finite A then (SOME listA. set listA = A) else undefined) f" |
"Diamond (after R Q) f = Diamond R (Diamond Q f)" |
"Diamond (union R Q) f = or (Diamond R f) (Diamond Q f)" |
"Diamond (repeat R) f =  mu (or (Diamond R (var 0)) (shiftup f 0))" 

lemma Diamondlist_eq_exist : "\<lbrakk>Diamondlist A f\<rbrakk> M e = {s. \<exists> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; simp; auto)

lemma Diamond_eq_exist [iff] : "finite A \<Longrightarrow>
\<lbrakk>Diamond (acts A) f\<rbrakk> M e = {s. \<exists> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Diamondlist_eq_exist)
  apply (rule someI2_ex; simp add: finite_list)
  done

fun Boxlist :: "'a list \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where
"Boxlist [] f = tt" |
"Boxlist (a # as) f = and' (box a f) (Boxlist as f)"

fun Box :: "'a regularformula \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where 
"Box eps f = f" |
"Box (acts A) f = Boxlist (if finite A then (SOME listA. set listA = A) else []) f" |
"Box (after R Q) f = Box R (Box Q f)" |
"Box (union R Q) f = and' (Box R f) (Box Q f)" |
"Box (repeat R) f =  nu (and' (Box R (var 0)) (shiftup f 0))" 

lemma Boxlist_eq_forall : "\<lbrakk>Boxlist A f\<rbrakk> M e = {s. \<forall> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; simp; auto)

lemma Box_eq_forall [simp] : "finite A \<Longrightarrow>
\<lbrakk>Box (acts A) f\<rbrakk> M e = {s. \<forall> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Boxlist_eq_forall)
  apply (rule someI2_ex; simp add: finite_list)
  done

fun negvari :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "(negvari tt i) = tt " |
  "(negvari ff i) = ff" |
  "(negvari (var X) i)  = (if i = X then (neg (var X)) else (var X))" |
  "(negvari (neg f) i) = neg (negvari f i)" |
  "(negvari (and' f f') i) = and' (negvari f i) (negvari f' i) " |
  "(negvari (or f f') i) = or (negvari f i) (negvari f' i)" |
  "(negvari (diamond act f) i) = diamond act (negvari f i) " |
  "(negvari (box act f) i) = box act (negvari f i)" |
  "(negvari (nu f) i) = nu (negvari f (Suc i))" |
  "(negvari (mu f) i) = mu (negvari f (Suc i))"

value "negvari (or (var 0) (mu (and' (var 0) (var 1)))) 0 :: nat formula"

fun occursvari :: "'a formula \<Rightarrow> nat \<Rightarrow> bool "
where 
  "(occursvari tt i) = False " |
  "(occursvari ff i) = False" |
  "(occursvari (var X) i) = (i = X)" |
  "(occursvari (neg f) i) = (occursvari f i)" |
  "(occursvari (and' f f') i) = ((occursvari f i) \<or> (occursvari f' i))" |
  "(occursvari (or f f') i) = ((occursvari f i) \<or> (occursvari f' i))" |
  "(occursvari (diamond act f) i) = (occursvari f i) " |
  "(occursvari (box act f) i) = (occursvari f i)" |
  "(occursvari (nu f) i) = (occursvari f (Suc i))" |
  "(occursvari (mu f) i) = (occursvari f (Suc i))"

lemma notoccursnuandmu [simp] :
assumes "\<forall>i e. \<not> occursvari (f :: 'a formula) i \<longrightarrow> (formulasemantics f M e = formulasemantics f M (e(i := S')))" 
shows "\<sigma> \<in> {nu, mu} \<Longrightarrow>  \<not> occursvari (\<sigma> f) i \<longrightarrow> (formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))"
proof
  assume assum1 : "(\<sigma> :: ('a formula => 'a formula)) \<in> {nu, mu}"
  assume assum2: "\<not> occursvari (\<sigma> f) i"
  hence "\<not> occursvari f (Suc i)" using assum1 by (cases "\<sigma> = mu") simp_all      
  hence "(\<forall> S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M ((newenvironment e S'') ((Suc i) := S')))" using assms by metis
  hence con1: "\<forall> S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M (newenvironment (e(i := S')) S'')" by simp
  show "(formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))"
    apply (cases "\<sigma> = mu")
    apply (simp add: con1) 
    apply (subgoal_tac "\<sigma> = nu")
    apply (simp add: con1) 
    using assum1 apply blast
    done
qed

lemma notoccurs [simp] : "(\<not>(occursvari f i) \<longrightarrow> (formulasemantics f M e = formulasemantics f M (e(i := S'))))"
  apply (induct f arbitrary: e i S')
  prefer 9
  using notoccursnuandmu apply blast
  prefer 9
  using notoccursnuandmu apply blast
  apply (simp_all)
  done

lemma notoccurseqnu :
  assumes "\<not>(occursvari f 0)"
  shows "formulasemantics f M (newenvironment e S') = formulasemantics (nu f) M e"
  apply simp
proof-
  have "\<forall>S''. formulasemantics f M (newenvironment e S') = formulasemantics f M ((newenvironment e S') (0 := S''))" using assms notoccurs by metis
  hence "\<forall>S''. formulasemantics f M ((newenvironment e S'')) = formulasemantics f M (newenvironment e S')" using newenvironmentswitchzero by auto
  hence "\<Union> {S''. S'' \<subseteq> formulasemantics f M (newenvironment e S'')} = \<Union> {S''. S'' \<subseteq> formulasemantics f M (newenvironment e S')}" by blast
  moreover have "... = formulasemantics f M (newenvironment e S')" by auto
  ultimately show "formulasemantics f M (newenvironment e S') = \<Union> {S'. S' \<subseteq> formulasemantics f M (newenvironment e S')}" by auto
qed

lemma notoccurseqmu :
  assumes "\<not>(occursvari f 0)"
  shows "formulasemantics f M (newenvironment e S') = formulasemantics (mu f) M e"
  apply simp
proof-
  have "\<forall>S''. formulasemantics f M (newenvironment e S') = formulasemantics f M ((newenvironment e S') (0 := S''))" using assms notoccurs by metis
  hence "\<forall>S''. formulasemantics f M ((newenvironment e S'')) = formulasemantics f M (newenvironment e S')" using newenvironmentswitchzero by auto
  hence "\<Inter> {S''. formulasemantics f M (newenvironment e S'') \<subseteq> S''} = \<Inter> {S''. formulasemantics f M (newenvironment e S') \<subseteq> S''}" by blast
  moreover have "... = formulasemantics f M (newenvironment e S')" by auto
  ultimately show "formulasemantics f M (newenvironment e S') = \<Inter> {S'. formulasemantics f M (newenvironment e S') \<subseteq> S'}" by auto
qed

fun alloccursposnegi :: "'a formula \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool"
where 
  "(alloccursposnegi tt i b) = True " |
  "(alloccursposnegi ff i b) = True" |
  "(alloccursposnegi (var X) i b) = ((X \<noteq> i) \<or> b)" |
  "(alloccursposnegi (neg f) i b) = (alloccursposnegi f i (\<not>b))" |
  "(alloccursposnegi (and' f f') i b) = ((alloccursposnegi f i b) \<and> (alloccursposnegi f' i b))" |
  "(alloccursposnegi (or f f') i b) = ((alloccursposnegi f i b) \<and> (alloccursposnegi f' i b))" |
  "(alloccursposnegi (diamond act f) i b) = (alloccursposnegi f i b) " |
  "(alloccursposnegi (box act f) i b) = (alloccursposnegi f i b)" |
  "(alloccursposnegi (nu f) i b) = (alloccursposnegi f (Suc i) b)" |
  "(alloccursposnegi (mu f) i b) = (alloccursposnegi f (Suc i) b)"

value "alloccursposnegi (nu (and' (neg (var 1)) (var 0))) 0 True"
value "alloccursposnegi (nu (and' (neg (var 1)) (var 0))) 0 False"

definition transformer :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's set "
  where
"transformer f M e S' = formulasemantics f M (newenvironment e S')"

lemma boxsubset : "(\<lbrakk>f\<rbrakk> M e \<subseteq> \<lbrakk>g\<rbrakk> M e') \<Longrightarrow>  \<lbrakk>box act f\<rbrakk> M e \<subseteq> \<lbrakk>box act g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (auto)
  done

lemma diamondsubset : "(\<lbrakk>f\<rbrakk> M e \<subseteq> \<lbrakk>g\<rbrakk> M e') \<Longrightarrow>  \<lbrakk>diamond act f\<rbrakk> M e \<subseteq> \<lbrakk>diamond act g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (auto)
  done

lemma nusubset : "(\<forall>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> \<lbrakk>g\<rbrakk> M (newenvironment e' S')) \<Longrightarrow> \<lbrakk>nu f\<rbrakk> M e \<subseteq> \<lbrakk>nu g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (auto)
  done

lemma musubset : "(\<forall>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> \<lbrakk>g\<rbrakk> M (newenvironment e' S')) \<Longrightarrow> \<lbrakk>mu f\<rbrakk> M e \<subseteq> \<lbrakk>mu g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (blast)
  done

lemma notoccursposneg : "\<not>occursvari f i \<longrightarrow> alloccursposnegi f i True \<and> alloccursposnegi f i False"
  by (induct f arbitrary: i; simp)

definition dependvari :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> nat \<Rightarrow> bool" where
"dependvari f M i = (\<exists>e S'. \<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M (e(i := S')))"

lemma transformerdef : "transformer f M e = (\<lambda>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S'))"
  by (meson transformer_def)

lemma notdependsmono : "\<not>dependvari f M i \<Longrightarrow>
  mono (\<lambda>S.(formulasemantics f M (e(i := S)))) \<and> antimono (\<lambda>S.(formulasemantics f M (e(i := S))))"
  apply (induct f arbitrary: i)
  apply (simp_all add : dependvari_def monotone_def)
  done

lemma notdependscoro : "(\<not>dependvari f M 0 \<longrightarrow> mono (transformer f M e))"
  apply (simp add: transformerdef)
proof-
  have "\<forall>S''. \<not>dependvari f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using notdependsmono by metis
  thus "\<not>dependvari f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

lemma andsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<and> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>1 \<and> A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>2"
  using assms by blast

lemma orsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<or> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<subseteq> B\<^sub>1 \<union> B\<^sub>2 \<or> A\<^sub>2 \<subseteq> B\<^sub>1 \<union> B\<^sub>2"
  using assms by blast

lemma monotonicity :
"(alloccursposnegi f i True \<longrightarrow> mono (\<lambda>S'.(formulasemantics f M (e(i := S')))))
 \<and> (alloccursposnegi f i False \<longrightarrow> antimono (\<lambda>S'.(formulasemantics f M (e(i := S')))))"
  apply (simp add: monotone_def)
  apply (induct f arbitrary : i e)
  prefer 7
  apply (meson alloccursposnegi.simps(8) boxsubset)
  prefer 7
  apply (meson alloccursposnegi.simps(7) diamondsubset)
  prefer 7
  apply (metis alloccursposnegi.simps(9) nusubset newenvironmentswitchsuccessor)
  prefer 7
  apply (metis alloccursposnegi.simps(10) musubset newenvironmentswitchsuccessor)
  apply (simp_all)
  apply (meson andsubset)
  apply (meson orsubset)
  done

lemma monotonicitycoro : "(alloccursposnegi f 0 True \<longrightarrow> mono (transformer f M e))
 \<and> (alloccursposnegi f 0 False \<longrightarrow> antimono (transformer f M e))"
  apply (simp add: transformerdef)
proof
  have "\<forall>S''. alloccursposnegi f 0 True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicity by metis
  thus "alloccursposnegi f 0 True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
next
  have "\<forall>S''. alloccursposnegi f 0 False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicity by metis
  thus "alloccursposnegi f 0 False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

end
theory mucalculus
imports Main "HOL-Library.Omega_Words_Fun"
begin

section \<open>formulas\<close>

datatype 'a regularformula =
  eps | acts "'a list" |
  after "'a regularformula" "'a regularformula"| 
  union "'a regularformula" "'a regularformula" | 
  repeat "'a regularformula"

(* from "HOL-Library.Regular-Sets.Regular_Exp" *)
definition conc :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr \<open>@@\<close> 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

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
"regformtolanguage (acts []) = {}" |
"regformtolanguage (acts (a#as)) = {[a]} \<union> regformtolanguage (acts (as))" |
"regformtolanguage (after R Q) = ({r @ q |r q. (r \<in> regformtolanguage R) \<and> (q \<in> regformtolanguage Q)})" |
"regformtolanguage (union R Q) = (regformtolanguage R) \<union> (regformtolanguage Q)" |
"regformtolanguage (repeat R) = (\<Union>n. (regformtolanguage R) ^^ n)"

lemma regformtolanguage_acts : "regformtolanguage (acts A) = {[a] | a. a \<in> set A}"
  apply (induct A)
  apply (simp_all)
  apply (blast)
  done

value "regformtolanguage (eps) :: nat list set" 
value "regformtolanguage (after (acts [1, 2]) (acts [3, 4])) :: nat list set" 

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
"(newenvironment e S'')((Suc i) := S') = newenvironment (e(i :=  S')) S''"
proof
  fix n
  show "((newenvironment e S'')((Suc i) := S')) n = (newenvironment (e(i :=  S')) S'') n"
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

fun Diamondlist :: "'a list \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where
"Diamondlist [] f = ff" |
"Diamondlist (a # as) f = or (diamond a f) (Diamondlist as f)"

definition Diamond :: "'a set \<Rightarrow> 'a formula \<Rightarrow> 'a formula "
  where "Diamond A f = Diamondlist (if finite A then (SOME listA. set listA = A) else []) f"

lemma Diamondlist_eq_exist : "\<lbrakk>Diamondlist A f\<rbrakk> M e = {s. \<exists> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (induct A)
  apply (simp_all)
  apply (auto)
  done

lemma Diamond_eq_exist : "finite A \<Longrightarrow>
\<lbrakk>Diamond A f\<rbrakk> M e = {s. \<exists> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Diamond_def Diamondlist_eq_exist)
  apply (rule someI2_ex)
  apply (simp_all add: finite_list)
  done

fun Boxlist :: "'a list \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where
"Boxlist [] f = tt" |
"Boxlist (a # as) f = and' (box a f) (Boxlist as f)"

definition Box :: "'a set \<Rightarrow> 'a formula \<Rightarrow> 'a formula "
  where "Box A f = Boxlist (if finite A then (SOME listA. set listA = A) else []) f"

lemma Boxlist_eq_forall : "\<lbrakk>Boxlist A f\<rbrakk> M e = {s. \<forall> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (induct A)
  apply (simp_all)
  apply (auto)
  done

lemma Box_eq_forall : "finite A \<Longrightarrow>
\<lbrakk>Box A f\<rbrakk> M e = {s. \<forall> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp only: Box_def Boxlist_eq_forall)
  apply (rule someI2_ex)
  apply (simp_all add: finite_list)
  done

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
proof-
  assume assum1 : "(\<sigma> :: ('a formula => 'a formula)) \<in> {nu, mu}"
  show "\<not> occursvari (\<sigma> (f :: 'a formula)) i \<longrightarrow> (formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))"
  proof
    assume assum2: "\<not> occursvari (\<sigma> f) i"
    hence "\<not> occursvari f (Suc i)" using assum1 by (cases "\<sigma> = mu") simp_all      hence "(\<forall> S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M ((newenvironment e S'') ((Suc i) := S')))" using assms by blast
    hence con1: "\<forall> S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M (newenvironment (e(i := S')) S'')" by simp
    show "(formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))"
    proof-
      have con2 : "\<forall>S''. formulasemantics f M (newenvironment e S'') = formulasemantics f M (newenvironment (e(i := S')) S'')" using con1 by auto
      hence "\<Union> {S''. S'' \<subseteq> formulasemantics f M (newenvironment e S'')} =  \<Union> {S''. S'' \<subseteq> formulasemantics f M (newenvironment (e(i := S')) S'')}" by auto
      hence "(formulasemantics (nu f) M e = formulasemantics (nu f) M (e(i := S')))" by simp
      moreover have "\<Inter> {S''. S'' \<supseteq> formulasemantics f M (newenvironment e S'')} =  \<Inter> {S''. S'' \<supseteq> formulasemantics f M (newenvironment (e(i := S')) S'')}" using con2 by auto
      from this moreover have "(formulasemantics (mu f) M e = formulasemantics (mu f) M (e(i := S')))" by simp
      ultimately show "(formulasemantics (\<sigma> f) M e = formulasemantics (\<sigma> f) M (e(i := S')))" using assum1 by auto
    qed
  qed
qed

lemma notoccurs [simp] : "(\<not>(occursvari f i) \<longrightarrow> (formulasemantics f M e = formulasemantics f M (e(i := S'))))"
  apply (induct f arbitrary: e i S')
  prefer 9
  using notoccursnuandmu apply blast
  prefer 9
  using notoccursnuandmu apply blast 
  apply (simp_all)
  done

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

fun closedupuntili :: "'a formula \<Rightarrow> nat \<Rightarrow> bool"
where 
  "(closedupuntili tt i) = True " |
  "(closedupuntili ff i) = True" |
  "(closedupuntili (var X) i) = (X < i)" |
  "(closedupuntili (neg f) i) = (closedupuntili f i)" |
  "(closedupuntili (and' f f') i) = ((closedupuntili f i) \<and> (closedupuntili f' i))" |
  "(closedupuntili (or f f') i) = ((closedupuntili f i) \<and> (closedupuntili f' i))" |
  "(closedupuntili (diamond act f) i) = (closedupuntili f i) " |
  "(closedupuntili (box act f) i) = (closedupuntili f i)" |
  "(closedupuntili (nu f) i) = (closedupuntili f (Suc i))" |
  "(closedupuntili (mu f) i) = (closedupuntili f (Suc i))"

definition closed :: "'a formula \<Rightarrow> bool"
  where "closed f = closedupuntili f 0"

value "closed (mu (var 0))"
value "closed (nu (and' (var 1) (var 0)))"

fun alloccursposneg :: "'a formula \<Rightarrow> bool \<Rightarrow> bool"
where 
  "(alloccursposneg tt b) = True " |
  "(alloccursposneg ff b) = True" |
  "(alloccursposneg (var X) b) = b" |
  "(alloccursposneg (neg f) b) = (alloccursposneg f (\<not>b))" |
  "(alloccursposneg (and' f f') b) = ((alloccursposneg f b) \<and> (alloccursposneg f' b))" |
  "(alloccursposneg (or f f') b) = ((alloccursposneg f b) \<and> (alloccursposneg f' b))" |
  "(alloccursposneg (diamond act f) b) = (alloccursposneg f b) " |
  "(alloccursposneg (box act f) b) = (alloccursposneg f b)" |
  "(alloccursposneg (nu f) b) = (alloccursposneg f b)" |
  "(alloccursposneg (mu f) b) = (alloccursposneg f b)"

fun alloccursposnegupuntili :: "'a formula \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool"
where 
  "(alloccursposnegupuntili tt i b) = True " |
  "(alloccursposnegupuntili ff i b) = True" |
  "(alloccursposnegupuntili (var X) i b) = ((X \<ge> i) \<or> b)" |
  "(alloccursposnegupuntili (neg f) i b) = (alloccursposnegupuntili f i (\<not>b))" |
  "(alloccursposnegupuntili (and' f f') i b) = ((alloccursposnegupuntili f i b) \<and> (alloccursposnegupuntili f' i b))" |
  "(alloccursposnegupuntili (or f f') i b) = ((alloccursposnegupuntili f i b) \<and> (alloccursposnegupuntili f' i b))" |
  "(alloccursposnegupuntili (diamond act f) i b) = (alloccursposnegupuntili f i b) " |
  "(alloccursposnegupuntili (box act f) i b) = (alloccursposnegupuntili f i b)" |
  "(alloccursposnegupuntili (nu f) i b) = (alloccursposnegupuntili f (Suc i) b)" |
  "(alloccursposnegupuntili (mu f) i b) = (alloccursposnegupuntili f (Suc i) b)"

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

value "alloccursposneg (mu (var 0)) True"
value "alloccursposneg (nu (and' (neg (var 1)) (var 0))) True"
value "alloccursposneg (nu (and' (neg (var 1)) (var 0))) False"
value "alloccursposnegupuntili (nu (and' (neg (var 1)) (var 0))) 0 True"
value "alloccursposnegupuntili (nu (and' (neg (var 1)) (var 0))) 0 False"

definition transformer :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's set "
  where
"transformer f M e S' = formulasemantics f M (newenvironment e S')"

lemma andsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<and> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>1 \<and> A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>2"
  using assms by blast

lemma orsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<or> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<subseteq> B\<^sub>1 \<union> B\<^sub>2 \<or> A\<^sub>2 \<subseteq> B\<^sub>1 \<union> B\<^sub>2"
  using assms by blast

lemma boxsubset : "(\<lbrakk>f\<rbrakk> M e \<subseteq> \<lbrakk>g\<rbrakk> M e') \<Longrightarrow>  \<lbrakk>box act f\<rbrakk> M e \<subseteq> \<lbrakk>box act g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (auto)
  done

lemma diamondsubset : "(\<lbrakk>f\<rbrakk> M e \<subseteq> \<lbrakk>g\<rbrakk> M e') \<Longrightarrow>  \<lbrakk>diamond act f\<rbrakk> M e \<subseteq> \<lbrakk>diamond act g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (auto)
  done

lemma nusubset : "(\<forall>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> \<lbrakk>g\<rbrakk> M (newenvironment e' S')) \<Longrightarrow>  \<lbrakk>nu f\<rbrakk> M e \<subseteq> \<lbrakk>nu g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (auto)
  done

lemma musubset : "(\<forall>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> \<lbrakk>g\<rbrakk> M (newenvironment e' S')) \<Longrightarrow>  \<lbrakk>mu f\<rbrakk> M e \<subseteq> \<lbrakk>mu g\<rbrakk> M e'"
  apply (simp add: formulasemantics.cases)
  apply (blast)
  done

lemma notoccursposneg : "\<not>occursvari f i \<longrightarrow> alloccursposnegi f i True \<and> alloccursposnegi f i False"
  apply (induct f arbitrary: i)
  apply (simp_all)
  done

definition dependvari :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> nat \<Rightarrow> bool" where
"dependvari f M i = (\<exists>e S'. \<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M (e(i := S')))"

lemma notdependsmono : "\<not>dependvari f M i \<Longrightarrow>
  mono (\<lambda>S.(formulasemantics f M (e(i := S)))) \<and> antimono (\<lambda>S.(formulasemantics f M (e(i := S))))"
  apply (induct f arbitrary: i)
  apply (simp_all add : dependvari_def monotone_def)
  done

lemma monotonicity :
"(alloccursposnegi f i True \<longrightarrow> mono (\<lambda>S'.(formulasemantics f M (e(i := S')))))
 \<and> (alloccursposnegi f i False \<longrightarrow> antimono (\<lambda>S'.(formulasemantics f M (e(i := S')))))"
  apply (simp add: monotone_def)
  apply (induct f arbitrary : i e)
  prefer 9
  apply (metis alloccursposnegi.simps(9) nusubset newenvironmentswitchsuccessor)
  prefer 9
  apply (metis alloccursposnegi.simps(10) musubset newenvironmentswitchsuccessor)
  prefer 7
  apply (meson alloccursposnegi.simps(8) boxsubset)
  prefer 7
  apply (meson alloccursposnegi.simps(7) diamondsubset)
  apply (simp_all)
  apply (meson andsubset)
  apply (meson orsubset)
  done

lemma transformerdef : "transformer f M e = (\<lambda>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S'))"
  by (meson transformer_def)

lemma monotonicitycoro : "(alloccursposnegi f 0 True \<longrightarrow> mono (transformer f M e))
 \<and> (alloccursposnegi f 0 False \<longrightarrow> antimono (transformer f M e))"
  apply (simp_all add: transformerdef)
proof
  have "\<forall>S''. alloccursposnegi f 0 True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicity by metis
  thus "alloccursposnegi f 0 True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
next
  have "\<forall>S''. alloccursposnegi f 0 False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicity by metis
  thus "alloccursposnegi f 0 False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

section \<open>paths\<close>

type_synonym ('a, 's) finpath = "('s \<times> 'a \<times> 's) list"
type_synonym ('a, 's) infpath = "('s \<times> 'a \<times> 's) word"

definition source :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'a" where
"source t = fst t"

definition action :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'b" where
"action t = fst (snd t)"

definition target :: "('a \<times> 'b \<times> 'c) \<Rightarrow> 'c" where
"target t = snd (snd t)"

fun validfinpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) finpath \<Rightarrow> 's \<Rightarrow> bool" where
"validfinpath M s [] s' = (s = s')" |
"validfinpath M s (t#ts) s' = (s = source t  \<and> t \<in> transition M \<and> validfinpath M (target t) ts s')"

definition validinfpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) infpath \<Rightarrow> bool" where
"validinfpath M s p = (source (p 0) = s \<and> (\<forall>n. p n \<in> transition M \<and> (target (p n) = source (p (Suc n)))))"

datatype ('a, 's) path = fin "('a, 's) finpath" | inf "('a, 's) infpath"

(*fun validpath :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where 
"validpath M s (fin p) = (\<exists>s'. validfinpath M s p s')" |
"validpath M s (inf p) = validinfpath M s p"*)

definition enabledactions :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set" where
"enabledactions M s = {a . (\<exists>s'. (s, a, s') \<in> transition M)}"

definition locked :: "('a, 's) lts \<Rightarrow> 'a set \<Rightarrow> 's \<Rightarrow> bool" where
"locked M B s = (enabledactions M s \<subseteq> B)"

fun progressing :: "('a, 's) lts \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"progressing M s B (fin p) = (\<exists>s'. validfinpath M s p s' \<and> locked M B s)" |
"progressing M s B (inf p) = validinfpath M s p"

definition match :: "'a regularformula \<Rightarrow> ('a, 's) finpath \<Rightarrow> bool" where
"match \<rho> p = (map action p \<in> regformtolanguage \<rho>)"

fun pref :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) finpath" where 
"pref i (fin p) = take i p" |
"pref i (inf p) = prefix i p"

fun suff :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('a, 's) path" where 
"suff i (fin p) = fin (drop i p)" |
"suff i (inf p) = inf (suffix i p)"

fun ind :: "nat \<Rightarrow> ('a, 's) path \<Rightarrow> ('s \<times> 'a \<times> 's)" where 
"ind i (fin p) = p!i" |
"ind i (inf p) = p i"

fun occurs :: "'a set \<Rightarrow> ('a, 's) path \<Rightarrow> bool" where
"occurs A (fin p) = (\<exists> a \<in> A. a \<in> (set (map action p)))" |
"occurs A (inf p) = (\<exists> n. (action (p n)) \<in> A)" 

fun freeuntiloccurence :: "('a, 's) path \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"freeuntiloccurence p \<alpha>\<^sub>f \<alpha>\<^sub>e = ((\<exists>i. \<not>(occurs \<alpha>\<^sub>f (fin (pref i p))) \<and> action (ind i p) \<in> \<alpha>\<^sub>e)
  \<or> \<not>(occurs \<alpha>\<^sub>f p))"

fun violating :: "('a, 's) path \<Rightarrow> 'a regularformula \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e = (\<exists>i. match \<rho> (pref i p) \<and> freeuntiloccurence (suff i p) \<alpha>\<^sub>f \<alpha>\<^sub>e)"

(*negate formulas*)

lemma negtrue : "formulasemantics (neg tt) M e = formulasemantics ff M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negfalse : "formulasemantics (neg ff) M e = formulasemantics tt M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negnegf : "formulasemantics (neg (neg (f))) M e = formulasemantics f M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negand' : "formulasemantics (neg (and' f f')) M e = formulasemantics (or (neg f) (neg f')) M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negor : "formulasemantics (neg (or f f')) M e = formulasemantics (and' (neg f) (neg f')) M e"
  apply (simp add: formulasemantics.cases)
  done

lemma negdiamond : "formulasemantics (neg (diamond act f)) M e = formulasemantics (box act (neg f)) M e"
  apply (simp add: formulasemantics.cases)
  apply auto
  done

lemma negbox : "formulasemantics (neg (box act f)) M e = formulasemantics (diamond act (neg f)) M e"
  apply (simp add: formulasemantics.cases)
  apply auto
  done

lemma complementuniontoexists [simp] : "s \<in> -(\<Union> {S. P S}) = (\<not>(\<exists> S. P S \<and> s \<in> S))"
  apply auto
  done 

lemma intersectiontoforall [simp] : "s \<in> (\<Inter> {S. P S}) = (\<forall> S. P S \<longrightarrow> s \<in> S)"
  apply auto
  done

lemma switchcomplementnegationnu [simp] :
  assumes  "(\<And> e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e)"
  shows    "formulasemantics (neg (nu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (nu f)) i ) M e"
proof-
have "\<And> S. (formulasemantics f M (newenvironment (e(i := - e i)) S)
   = formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))))" by (simp only : newenvironmentsuccessorcomplement)
hence "\<And> S. ((formulasemantics f M (newenvironment (e(i := - e i)) S) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S)))" using assms by blast
thus "formulasemantics (neg (nu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (nu f)) i) M e" by simp 
qed

lemma switchcomplementnegationmu [simp] :
  assumes  "(\<And> e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e)"
  shows    "formulasemantics (neg (mu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (mu f)) i) M e"
proof-
have "\<And> S. (formulasemantics f M (newenvironment (e(i := - e i)) S)
   = formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))))" by (simp only : newenvironmentsuccessorcomplement)
hence "\<And> S. ((formulasemantics f M (newenvironment (e(i := - e i)) S) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S)))" using assms by blast
thus "formulasemantics (neg (mu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (mu f)) i) M e" by simp 
qed

(*this can be a lot shorter*)
lemma negnuinbetween [simp]  : "(formulasemantics (neg (nu f)) M e) = (\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))})"
proof-
  have "\<And>s. ((s \<in> (-\<Union> {S. S \<subseteq> formulasemantics f M (newenvironment e S)})) = (s \<in> (\<Inter> {S. - formulasemantics f M (newenvironment e (- S)) \<subseteq> S})))"
  proof -
    fix s
    have "(\<forall> S. S \<subseteq> formulasemantics f M (newenvironment e S) \<longrightarrow> s \<notin> S) = (\<forall> S. (- formulasemantics f M (newenvironment e (- S)) \<subseteq> S) \<longrightarrow> s \<in> S)"
    proof
      assume assum : "\<forall>S. S \<subseteq> formulasemantics f M (newenvironment e S) \<longrightarrow> s \<notin> S"
      show "\<forall>S. (- formulasemantics f M (newenvironment e (- S)) \<subseteq> S \<longrightarrow> s \<in> S)"
      proof
      fix S
      show "(- formulasemantics f M (newenvironment e (- S)) \<subseteq> S \<longrightarrow> s \<in> S)"
      proof
        assume "- formulasemantics f M (newenvironment e (- S)) \<subseteq> S"
        hence "- S \<subseteq> formulasemantics f M (newenvironment e (- S))" by auto
        thus "s \<in> S" using assum by auto
      qed
      qed
    next
      assume assum : "\<forall>S. -formulasemantics f M (newenvironment e (-S)) \<subseteq> S \<longrightarrow> s \<in> S"
      show "\<forall>S. (S \<subseteq> formulasemantics f M (newenvironment e S)  \<longrightarrow> s \<notin> S)"
      proof
      fix S
      show "(S \<subseteq> formulasemantics f M (newenvironment e S)  \<longrightarrow> s \<notin> S)"
      proof
        assume "S \<subseteq> formulasemantics f M (newenvironment e S)"
        hence h : "(-formulasemantics f M (newenvironment e (S))) \<subseteq> (-S)" by auto
        have "-formulasemantics f M (newenvironment e (-(-S))) \<subseteq> (-S) \<longrightarrow> s \<in> (-S)" using assum by blast
        thus "s \<notin> S" using h by auto
      qed
    qed
  qed
  hence "(\<not>(\<exists> S. S \<subseteq> formulasemantics f M (newenvironment e S) \<and> s \<in> S)) = (\<forall> S. (- formulasemantics f M (newenvironment e (- S)) \<subseteq> S) \<longrightarrow> s \<in> S)" by auto
  thus "(s \<in> (-\<Union> {S. S \<subseteq> formulasemantics f M (newenvironment e S)})) = (s \<in> (\<Inter> {S. - formulasemantics f M (newenvironment e (- S)) \<subseteq> S}))" by simp
qed
  from this have "(-\<Union> {S. S \<subseteq> formulasemantics f M (newenvironment e S)}) = (\<Inter> {S. - formulasemantics f M (newenvironment e (- S)) \<subseteq> S})" by blast
    thus ?thesis by (simp add: formulasemantics.cases)
qed

(*and this one*)
lemma negnu : "formulasemantics (neg (nu f)) M e = formulasemantics (mu (neg (negvari f 0))) M e"
proof-
  have h : "formulasemantics (neg (nu f)) M e = (\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))})" using negnuinbetween by simp
  have "\<forall> e i. (formulasemantics (neg f) M (e(i := -e(i)))) = formulasemantics (negvari (neg f) i) M e"  
  proof
    (induct_tac f)
      show "\<forall> e i. (formulasemantics (neg tt) M (e(i := -e(i)))) =  (formulasemantics (negvari (neg tt) i) M e)" by simp
    next
      show "\<forall> e i. formulasemantics (neg ff) M (e(i := -e(i))) = formulasemantics (negvari (neg ff) i) M e" by auto
    next
      show "\<And>X. \<forall> e i. formulasemantics (neg (var X)) M (e(i := -e(i))) =  formulasemantics (negvari (neg (var X)) i) M e"
        by (simp add: formulasemantics.cases newenvironment.cases negvari.cases)
    next
      show "\<And>f. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) =  formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (neg f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (neg f)) i) M e" by simp
    next 
      show "\<And>f f'. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg f')  M (e(i := -e(i))) = formulasemantics (negvari (neg f') i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (and' f f')) M (e(i := -e(i))) = formulasemantics (negvari (neg (and' f f')) i) M e" by simp
    next 
      show "\<And>f f'. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg f')  M (e(i := -e(i))) = formulasemantics (negvari (neg f') i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (or f f')) M (e(i := -e(i))) = formulasemantics (negvari (neg (or f f')) i) M e" by simp
    next
      show "\<And>act f.\<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (box act f)) M  (e(i := -e(i))) = formulasemantics (negvari (neg (box act f)) i) M e" by simp
    next 
      show "\<And>act f.\<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (diamond act f)) M  (e(i := -e(i))) = formulasemantics (negvari (neg (diamond act f)) i) M e" by simp
    next 
      have "\<And>f. (\<forall>e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e) \<longrightarrow>
        (\<forall> e i. formulasemantics (neg (nu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (nu f)) i ) M e)" using switchcomplementnegationnu by blast
      thus "\<And>f. \<forall>e i. formulasemantics (neg f) M (e(i := - e i)) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall>e i. formulasemantics (neg (nu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (nu f)) i) M e" by simp
    next 
      have "\<And>f. (\<forall>e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e) \<longrightarrow>
        (\<forall> e i. formulasemantics (neg (mu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (mu f)) i ) M e)" using switchcomplementnegationmu by blast
      thus "\<And>f. \<forall> e i. formulasemantics (neg f) M (e(i := -e(i))) = formulasemantics (negvari (neg f) i) M e \<Longrightarrow>
        \<forall> e i. formulasemantics (neg (mu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (mu f)) i ) M e" by simp
  qed
  hence "\<And> S. formulasemantics (neg f) M ((newenvironment e S)(0 := - (newenvironment e S) 0)) =
     formulasemantics (negvari (neg f) 0) M (newenvironment e S)" by blast
  hence "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (negvari (neg f) 0) M (newenvironment e S)" by (simp only : newenvironmentzerocomplement)  
  hence  "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (neg (negvari f 0)) M (newenvironment e S)" by auto
  hence "(\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))}) = (\<Inter> {S. S \<supseteq> (formulasemantics (neg (negvari f 0)) M (newenvironment e (S)))})" by auto
  thus ?thesis using h by auto
qed

lemma negvarnegvar [simp] : "formulasemantics (negvari (negvari f i) i) M e = formulasemantics f M e"
  apply (induct f arbitrary : i e) 
  apply (simp_all add : formulasemantics.cases)
  done

lemma negmu : "formulasemantics (neg (mu f)) M e = formulasemantics (nu (neg (negvari f 0))) M e"
proof-
  have "formulasemantics (mu (neg (negvari (neg (negvari f 0)) 0))) M e = formulasemantics (neg (nu (neg (negvari f 0)))) M e" by (simp only: negnu)
  hence "formulasemantics (neg (mu (neg (negvari (neg (negvari f 0)) 0)))) M e = formulasemantics (neg (neg (nu (neg (negvari f 0))))) M e" by auto
  also have "... = formulasemantics (nu (neg (negvari f 0))) M e" by (simp add : negnegf)
  ultimately show ?thesis by auto
qed

lemma gfp_eq_nu [simp] :
"gfp (transformer f M e) = formulasemantics (nu f) M e"
by (simp add: gfp_def transformer_def)

lemma lfp_eq_mu [simp] :
"lfp (transformer f M e) = formulasemantics (mu f) M e"
  by (simp add: lfp_def transformer_def)

lemma transformersubset : 
  assumes "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e) S' \<subseteq> S' \<longrightarrow> ((transformer f M e)^^(Suc i)) S' \<subseteq> ((transformer f M e)^^i) S') \<and>
    (S' \<subseteq> (transformer f M e) S' \<longrightarrow> ((transformer f M e)^^ i) S' \<subseteq> ((transformer f M e)^^(Suc i)) S')"
  apply (induct i)
  using assms apply (simp_all add: mono_def)
  done

lemma fpoweriplusn : 
  assumes "((f :: 'a \<Rightarrow> 'a)^^i) S' = (f^^(Suc i)) S'"
  shows "(f^^(i + n)) S' = (f^^(Suc i + n)) S'" 
  apply (induct n)
  using assms apply (simp)
proof-
  fix n
  assume "(f ^^ (i + n)) S' = (f ^^ (Suc i + n)) S'"
  hence "f ((f ^^ (i + n)) S') = f ((f ^^ Suc (i + n)) S')" by auto
  thus "(f ^^ (i + Suc n)) S' = (f ^^ (Suc i + Suc n)) S'" by auto
qed

lemma exists_fixpoint : 
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  and  "S' \<subseteq> (transformer f M e) S' \<or> (transformer f M e) S' \<subseteq> S'"
  shows "\<exists>n \<le> card(UNIV :: 's set). ((transformer f M e)^^n) S' = ((transformer f M e)^^(Suc n)) S'"
proof (rule ccontr)
  assume "\<not> (\<exists>n\<le>card(UNIV :: 's set).((transformer f M e ^^ n) S') = ((transformer f M e ^^ Suc n) S'))"
  hence assum1 : "\<forall>n\<le>card(UNIV :: 's set).((transformer f M e ^^ n) S') \<noteq> ((transformer f M e ^^ Suc n) S')" by auto
  have "S' \<subseteq> (transformer f M e) S' \<or> (transformer f M e) S' \<subseteq> S'" using assms(3) by auto
  moreover{
    assume assum2 : "S' \<subseteq> (transformer f M e) S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((transformer f M e ^^ n) S') \<ge> n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> n \<le> card ((transformer f M e ^^ n) S')"
        apply (induct n)
        apply (simp)
      proof
        fix n
        assume assum3: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> n \<le> card ((transformer f M e ^^ n) S')"
        assume assum4 : "Suc n \<le> Suc (card (UNIV :: 's set))"
        hence "n \<le> (card (UNIV :: 's set))" by auto
        hence "(transformer f M e ^^ n) S' \<noteq> (transformer f M e ^^ (Suc n)) S'" using assum1 by auto
        moreover have "(transformer f M e ^^ n) S' \<subseteq> (transformer f M e ^^ (Suc n)) S'" using assms(2) assum2 transformersubset by blast
        ultimately have "(transformer f M e ^^ n) S' \<subset> (transformer f M e ^^ (Suc n)) S'" using psubset_eq by auto
        moreover have "finite ((transformer f M e ^^ Suc n) S')" using assms(1) rev_finite_subset by auto
        ultimately have "card ((transformer f M e ^^ n) S') < card ((transformer f M e ^^ Suc n) S')" using psubset_card_mono by metis
        thus "Suc n \<le> card ((transformer f M e ^^ Suc n) S')" using assum3 assum4 by auto
      qed
    qed
    hence contradiction1 : "card ((transformer f M e ^^ Suc (card(UNIV :: 's set))) S') \<ge>  Suc (card(UNIV :: 's set))" by auto
    have contradiction2: "card ((transformer f M e ^^ Suc (card(UNIV :: 's set))) S') \<le> card(UNIV :: 's set)" using assms(1) card_mono by auto
    hence False using contradiction1 contradiction2 by auto
  }
  moreover{
    assume assum2 : "(transformer f M e) S' \<subseteq> S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((transformer f M e ^^ n) S') < Suc(card(UNIV :: 's set)) - n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> card ((transformer f M e ^^ n) S') < Suc (card(UNIV :: 's set)) - n"
        apply (induct n)
        apply (simp add : assms(1) card_mono less_Suc_eq_le)
      proof
        fix n
        assume assum3: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> card ((transformer f M e ^^ n) S') < Suc(card (UNIV :: 's set)) - n"
        assume assum4 : "Suc n \<le> Suc (card (UNIV :: 's set))"
        hence "n \<le> (card (UNIV :: 's set))" by auto
        hence "(transformer f M e ^^ n) S' \<noteq> (transformer f M e ^^ (Suc n)) S'" using assum1 by auto
        moreover have "(transformer f M e ^^ (Suc n)) S' \<subseteq> (transformer f M e ^^ n) S'" using assms(2) assum2 transformersubset by blast 
        ultimately have "(transformer f M e ^^ (Suc n)) S' \<subset> (transformer f M e ^^  n) S'" using psubset_eq by auto
        moreover have "finite ((transformer f M e ^^ n) S')" using assms(1) rev_finite_subset by auto
        ultimately have "card ((transformer f M e ^^ (Suc n)) S') < card ((transformer f M e ^^ n) S')" using psubset_card_mono by metis
        thus "card ((transformer f M e ^^ Suc n) S') < Suc(card (UNIV :: 's set)) - (Suc n)" using assum3 assum4 by auto
      qed
    qed
    hence "card ((transformer f M e ^^ Suc (card(UNIV :: 's set))) UNIV) <  0" by auto
    hence False by auto
  }
  ultimately show False by auto
qed

lemma gfp_transformer [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^(card (UNIV :: 's set)))(UNIV) = gfp (transformer f M e)"
proof-
  have "\<exists>n \<le> card(UNIV :: 's set). ((transformer f M e)^^n) (UNIV) = ((transformer f M e)^^(Suc n)) (UNIV)" using assms exists_fixpoint by blast
  from this obtain n where assum2: "n \<le> card (UNIV :: 's set) \<and>  ((transformer f M e)^^n) (UNIV) = ((transformer f M e)^^(Suc n)) (UNIV)" by auto
  hence "(transformer f M e ^^ (n + (card (UNIV :: 's set) - n))) (UNIV) = (transformer f M e ^^ (Suc n +  (card (UNIV :: 's set) - n))) (UNIV)" using fpoweriplusn by metis
  hence "((transformer f M e)^^(card (UNIV :: 's set)))(UNIV) = ((transformer f M e)^^Suc(card (UNIV :: 's set)))(UNIV)" using assum2 by auto
  thus ?thesis using gfp_Kleene_iter assms(2) by blast
qed

lemma lfp_transformer [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^(card (UNIV :: 's set))){} = lfp (transformer f M e)"
proof-
  have "\<exists>n \<le> card(UNIV :: 's set). ((transformer f M e)^^n) {} = ((transformer f M e)^^(Suc n)) {}" using assms exists_fixpoint by blast
  from this obtain n where assum2: "n \<le> card (UNIV :: 's set) \<and>  ((transformer f M e)^^n) {} = ((transformer f M e)^^(Suc n)) {}" by auto
  hence "(transformer f M e ^^ (n + (card (UNIV :: 's set) - n))) {} = (transformer f M e ^^ (Suc n +  (card (UNIV :: 's set) - n))) {}" using fpoweriplusn by metis
  hence "((transformer f M e)^^(card (UNIV :: 's set))){} = ((transformer f M e)^^Suc(card (UNIV :: 's set))){}" using assum2 by auto
  thus ?thesis using lfp_Kleene_iter assms(2) by blast
qed

lemma transformer_eq_nu [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^(card (UNIV :: 's set)))(UNIV) = formulasemantics (nu f) M e"
  using gfp_eq_nu gfp_transformer assms by auto  

lemma transformer_eq_mu [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^(card (UNIV :: 's set))){} = formulasemantics (mu f) M e"
  using lfp_eq_mu lfp_transformer assms by auto

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
  apply (induct f arbitrary : i)
  apply (simp_all)
  done

definition shiftdownenv :: "(nat \<Rightarrow> 's set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 's set) " where
"shiftdownenv e i n = (if n < i then e n else e (n + 1))"

lemma largerandsmaller : "X - Suc 0 < i \<Longrightarrow> \<not> X \<le> i \<Longrightarrow> (P :: nat \<Rightarrow> bool) X"
  by auto

lemma largerandsmallerenv' : "X - Suc 0 < i \<longrightarrow> \<not> X \<le> i \<longrightarrow> (e 0) = (e X)"
  using largerandsmaller by auto

lemma largerandsmallerenv [simp] : "X - Suc 0 < i \<longrightarrow> \<not> X \<le> i \<longrightarrow> (s \<in> e 0) = (s \<in> e X)"
  using largerandsmaller by auto

lemma shiftdownnewenv_eq_newenvshiftdown [simp] : "shiftdownenv (newenvironment e S') (Suc i) = newenvironment (shiftdownenv e i) S'"
  apply (rule)
  apply (induct_tac x)
  apply (simp_all add: shiftdownenv_def newenvironment.cases)
  done

lemma inbetweenlemma : "formulasemantics (shiftdown f (Suc i)) M (newenvironment (shiftdownenv e i) S') = 
  formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i))"
  by simp

lemma shiftdownlemma [simp] : "\<not>(occursvari f i) \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e)"
  apply (induct f arbitrary: e i)
  apply (simp_all add: shiftdownenv_def)
  apply (simp_all only : inbetweenlemma)
  using largerandsmallerenv' apply (metis)
  apply (rule impI)
  prefer 2 
  apply (rule impI)
proof-
  fix f e i
  assume assum1 : "(\<And>e i. \<not> occursvari f i \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "\<Inter> {S'. \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i)) \<subseteq> S'} = \<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S'}" using nusubset by auto
next
  fix f e i
  assume assum1 : "(\<And>e i. \<not> occursvari f i \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e))"
  assume assum2 : "\<not> occursvari f (Suc i)"
  hence "\<forall>S'. formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i)) = formulasemantics f M (newenvironment e S')" using assum1 by blast
  thus "\<Union> {S'. S' \<subseteq> \<lbrakk>shiftdown f (Suc i)\<rbrakk> M (shiftdownenv (newenvironment e S') (Suc i))} = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" using musubset by auto
qed

lemma shiftdownnewenv [simp] : "shiftdownenv (newenvironment e S') 0 = e"
  apply (rule)
  apply (simp add: shiftdownenv_def)
done

lemma shiftdowncoro : "\<not>(occursvari f 0) \<longrightarrow> (formulasemantics (shiftdown f 0) M e) = (formulasemantics f M (newenvironment e S'))" 
  using shiftdownlemma shiftdownnewenv by metis

lemma split [iff] : "t = (source t, action t, target t)" 
  by (simp add: source_def action_def target_def)

lemma targetpath [simp]: 
"validfinpath M s p s' \<longrightarrow> s' \<in> insert s (set (map target p))"
  apply (induct p arbitrary : s)
  apply (simp_all)
  done

lemma prop40rtl :
  assumes "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)"
  and "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "finite A"
  shows "(s \<in> formulasemantics (mu (and' g (or f (Diamond A (var 0))))) (M :: ('a, 's) lts) e)"
  apply (simp add : newenvironment.cases Diamond_eq_exist assms(4))
proof-
  from assms(1) obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set p \<subseteq> A)
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)" by auto
  show "\<forall>S'. formulasemantics g M (newenvironment e S') \<inter> (formulasemantics f M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<subseteq> S' \<longrightarrow> s \<in> S'"
    apply (rule allI)
    apply (rule impI)
  proof-
  fix S'
  assume assum2 : "formulasemantics g M (newenvironment e S') \<inter> (formulasemantics f M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<subseteq> S'"
  have inS' : "(validfinpath M s p s' \<and> (action ` set p \<subseteq> A)
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e) \<and> s' \<in> S') \<longrightarrow> s \<in> S'"
    apply (induct p arbitrary : s)
    apply (simp_all)
    apply (rule impI)
  proof-
    fix t p s
    assume assum3 : "(\<And>s. validfinpath M s p s' \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S' \<longrightarrow> s \<in> S')"
    assume assum4 : "s = source t \<and> t \<in> transition M \<and> validfinpath M (target t) p s' \<and> action t \<in> A \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target t \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S'"
    hence "target t \<in> S'" using assum3 by auto
    hence "(source t, action t, target t) \<in> transition M \<and> target t \<in> S'" using assum4 split by metis
    hence c1 : "source t \<in> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}" using assum4 split by auto
    have "source t \<in> formulasemantics (shiftdown g 0) M e" using assum4 by auto
    hence c2 : "source t \<in> formulasemantics g M (newenvironment e S')" using shiftdowncoro assms(3) by metis
    show "source t \<in> S'" using c1 c2 assum2 by auto
  qed
  have "s' \<in> insert s (set (map target p))" using targetpath assum1 by metis
  hence "s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> s' \<in> (formulasemantics (shiftdown f 0) M e)" using assum1 by auto
  hence "s' \<in> formulasemantics g M (newenvironment e S') \<and> s' \<in> formulasemantics f M (newenvironment e S')" using assms(2) assms(3) shiftdowncoro by metis
  hence "s' \<in> S'" using assum2 by auto
  thus "s \<in> S'" using assum1 inS' by auto
qed
qed

lemma prop40ltrinbetween :
  assumes "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "finite A"
  shows "s \<in> ((transformer (and' g (or f (Diamond A (var 0)))) M e)^^n){} \<longrightarrow>
  (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set p \<subseteq> A)
     \<and> s \<in> (formulasemantics (shiftdown g 0) M e)
     \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  apply (simp)
  apply (induct n arbitrary : s)
  apply (simp)
  apply (rule impI)
proof-
  fix n s
  assume assum1 : "\<And>s. s \<in> (transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {} 
    \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  assume assum2 : "s \<in> (transformer (and' g (or f (Diamond A (var 0)))) M e ^^ Suc n) {}"
  hence splitand : "(s \<in> formulasemantics g M (newenvironment e ((transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {}))) 
    \<and> (s \<in> formulasemantics f M (newenvironment e ((transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {})) \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {}))" by (simp add: transformer_def formulasemantics.cases Diamond_eq_exist assms(3))
  hence ing : "s \<in> (formulasemantics (shiftdown g 0) M e)" using shiftdowncoro assms by metis
  from splitand have "s \<in> formulasemantics f M (newenvironment e ((transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {})) \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {})" by auto
  moreover {
    assume assum3 : "s \<in> formulasemantics f M (newenvironment e ((transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {}))"
    from assum3 have "s \<in> (formulasemantics (shiftdown f 0) M e)" using shiftdowncoro assms by metis
    hence "validfinpath M s [] s \<and> s \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set [] \<subseteq> A) \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set []) \<subseteq> (formulasemantics (shiftdown g 0) M e)" using ing by simp
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set p) \<subseteq> (formulasemantics (shiftdown g 0) M e)" by blast
  }
  moreover {
    assume "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {}"
    from this obtain s' act where assum3 : "act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> (transformer (and' g (or f (Diamond A (var 0)))) M e ^^ n) {}" by auto
    hence "\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" using assum1 by auto
    from this obtain p s'' where tail : "validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" by auto
    let ?p = "(s, act, s') # p"
    have "source (s, act, s') = s \<and> (s, act, s') \<in> transition M \<and> validfinpath M (target (s, act, s')) p s''" using assum3 tail by (simp add : source_def target_def)
    hence "validfinpath M s ?p s''" by auto
    hence "validfinpath M s ?p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set ?p \<subseteq> A) \<and> 
      s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set ?p \<subseteq> (formulasemantics (shiftdown g 0) M e)" using assum3 ing tail by (simp add : target_def action_def)
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A 
      \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e)" by blast
  }
  ultimately show "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e)" using splitand by blast
qed

lemma monotonicityformula40 : 
  assumes  "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "finite A"
  shows "mono (transformer (and' g (or f (Diamond A (var 0)))) M e)"
  apply (simp add: Diamond_def assms(3))
proof-
  have "alloccursposnegi (and' g (or f (Diamondlist (SOME listA. set listA = A) (var 0)))) 0 True"
    apply (rule someI2_ex)
    apply (simp add: finite_list assms(3))
  proof-
    fix listA
    show "alloccursposnegi (and' g (formula.or f (Diamondlist listA (var 0)))) 0 True" 
      apply (induct_tac listA)
      apply (simp_all add: notoccursposneg assms)
      done
  qed
  thus "mono (transformer (and' g (or f (Diamondlist (SOME listA. set listA = A) (var 0)))) M e)" using monotonicitycoro by metis
qed

lemma prop40ltr :
  assumes "s \<in> formulasemantics (mu (and' g (or (f) (Diamond A (var 0))))) (M :: ('a, 's) lts) e"
  and "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "(\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) 
        \<and> (set (map action p) \<subseteq>  A) 
        \<and> (insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)))"
  apply (simp add : newenvironment.cases)
proof-
  have "mono (transformer (and' g (or f (Diamond A (var 0)))) M e)" using assms(2) assms(3) assms(5) monotonicityformula40 by metis
  hence "s \<in> ((transformer (and' g (or f (Diamond A (var 0)))) M e)^^(card (UNIV :: 's set))){}" using assms(1) assms(4) transformer_eq_mu by auto 
  thus "\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> formulasemantics (shiftdown f 0) M e
        \<and> action ` set p \<subseteq> A
        \<and> s \<in> formulasemantics (shiftdown g 0) M e
        \<and> target ` set p \<subseteq> formulasemantics (shiftdown g 0) M e" using prop40ltrinbetween assms(2) assms(3) assms(5) by metis
qed

(*simplifies independence to not occurs*)
lemma prop40 :
  assumes "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "(s \<in> formulasemantics (mu (and' g (or f (Diamond A (var 0))))) (M :: ('a, 's) lts) e) = 
    (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A) 
      \<and> (insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)))"
  apply (rule iffI)
  using assms prop40ltr apply metis
  using assms prop40rtl apply metis
  done

fun recursivepath :: "('s \<Rightarrow> 's \<times> 'a \<times> 's) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 's \<times> 'a \<times> 's" where
"recursivepath succ s 0 = succ s" | 
"recursivepath succ s (Suc n) = succ (target (recursivepath succ s n))"

lemma existssuccessor : 
"(\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>s'' act. act \<in> A \<and> (s', act, s'') \<in> (transition M) \<and> s'' \<in> S')) \<Longrightarrow>
(\<exists> succ.(\<forall>s'. s' \<in> S' \<longrightarrow> (succ s' \<in> (transition M) \<and> source(succ s') = s' \<and> action (succ s') \<in> A \<and> target (succ s') \<in> S')))"
proof-
  assume "\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>s'' act. act \<in> A \<and> (s', act, s'') \<in> (transition M) \<and> s'' \<in> S')"
  hence "(\<exists> succ actsucc.(\<forall>s'. s' \<in> S' \<longrightarrow> ((s', actsucc s', succ s') \<in> (transition M) \<and> succ s' \<in> S' \<and> actsucc s' \<in> A)))" by metis
  from this obtain succ actsucc where assum1 : "\<forall>s'. s' \<in> S' \<longrightarrow> ((s', actsucc s', succ s') \<in> (transition M) \<and> succ s' \<in> S'  \<and> actsucc s' \<in> A)" by auto
  let ?succ = "\<lambda>s. (s, actsucc s, succ s)"
  have "\<forall>s'. s' \<in> S' \<longrightarrow> ?succ s' \<in> transition M \<and> source (?succ s') = s' \<and> action (?succ s') \<in> A \<and> target (?succ s') \<in> S'"
    using assum1 by (simp add: source_def action_def target_def)
  thus "\<exists> succ.(\<forall>s'. s' \<in> S' \<longrightarrow> (succ s' \<in> (transition M) \<and> source(succ s') = s' \<and> action (succ s') \<in> A \<and> target (succ s') \<in> S'))" by auto
qed

lemma successorlemma [simp]: 
  assumes "(s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow> (\<exists>s'' act. act \<in> A \<and> (s', act, s'') \<in> (transition M) \<and> s'' \<in> S')))"
  shows "(\<exists> p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))"
  apply (simp add : validinfpath_def)
proof-
  have "\<exists> succ.(\<forall>s'. s' \<in> S' \<longrightarrow> (succ s' \<in> (transition M) \<and> source(succ s') = s' \<and> action (succ s') \<in> A \<and> target (succ s') \<in> S'))" using existssuccessor assms by auto
  from this obtain succ where assum1 : "\<forall>s'. s' \<in> S' \<longrightarrow> (succ s' \<in> (transition M) \<and> source(succ s') = s' \<and> action (succ s') \<in> A \<and> target (succ s') \<in> S')" by auto
  let ?p = "recursivepath succ s"
  have "source (?p 0) = s" using assum1 assms by simp
  moreover have "(\<forall>n. target(?p n) \<in> S' \<and> ?p n \<in> transition M \<and> target (?p n) = source (?p (Suc n)) \<and> action (?p n) \<in> A)"
  proof
    fix n
    show "target(?p n) \<in> S' \<and> ?p n \<in> transition M \<and> target (?p n) = source (?p (Suc n)) \<and> action (?p n) \<in> A"
      apply (induct n)
      using assum1 assms apply (simp)
    proof-
      fix n
      assume "target (recursivepath succ s n) \<in> S' \<and> recursivepath succ s n \<in> transition M \<and> target (recursivepath succ s n) = source (recursivepath succ s (Suc n)) \<and> action (recursivepath succ s n) \<in> A"
      thus "target (recursivepath succ s (Suc n)) \<in> S' \<and> recursivepath succ s (Suc n) \<in> transition M \<and> target (recursivepath succ s (Suc n)) = source (recursivepath succ s (Suc (Suc n))) \<and> action (recursivepath succ s (Suc n)) \<in> A" using assum1 by auto
    qed
  qed
  ultimately have "source (?p 0) = s \<and> (\<forall>n. ?p n \<in> transition M \<and> target (?p n) = source (?p (Suc n))) \<and> (\<forall>n. action (?p n) \<in> A)" by auto
  thus "\<exists>p. source (p 0) = s \<and> (\<forall>n. p n \<in> transition M \<and> target (p n) = source (p (Suc n))) \<and> (\<forall>n. action (p n) \<in> A)" by blast
qed 

lemma invariant : 
  assumes "\<not>(occursvari f 0)"
  and "S' \<subseteq> (\<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'})"
  and "s \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}"
  shows "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}"
proof-
  have "s \<in> (\<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'})" using assms(2) assms(3) by auto
  hence "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<or>  (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S')" using assms(2) by auto
  moreover have "s \<notin> \<lbrakk>f\<rbrakk> M (newenvironment e S')"
    apply (rule ccontr)
    apply (simp)
  proof-
    assume "s \<in> \<lbrakk>f\<rbrakk> M (newenvironment e S')"
    hence "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e" using assms(1) shiftdowncoro by metis
    hence "validfinpath M s [] s \<and> s \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action []) \<subseteq> A)" by auto
    thus False using assms(3) by blast
  qed
  ultimately have "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'" by auto
  from this obtain act s' where assum1 : "act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'" by auto
  have "\<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)"
    apply (rule ccontr)
    apply (simp)
  proof-
    assume "\<exists>p s''. s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> validfinpath M s' p s'' \<and> action ` set p \<subseteq> A"
    from this obtain p s'' where "s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> validfinpath M s' p s'' \<and> action ` set p \<subseteq> A" by auto
    hence "validfinpath M s ((s, act , s')#p) s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action ((s, act, s')#p)) \<subseteq> A)" using assum1 by (simp add : source_def action_def target_def)
    thus False using assms(3) by blast
  qed
  thus ?thesis using assum1 by auto
qed

lemma theorem21generalizedltr : 
  assumes "\<not>(occursvari f 0)"
  and "(s \<in> formulasemantics (nu (or f (Diamond A (var 0)))) M e)"
  and "finite A"
  shows "((\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or>
    (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))"
proof-
  have "\<exists>S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" using assms(2) by (simp add : Diamond_eq_exist assms(3))
  from this obtain S' where assum1 : "S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" by auto
  have "(\<nexists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<Longrightarrow>  (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))"
    apply (rule successorlemma)
  proof-
    assume assum2 : "\<nexists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A"
    let ?S' = "S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}" 
    have "(\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>s'' act. act \<in> A \<and> (s', act, s'') \<in> (transition M) \<and> s'' \<in> ?S')))"
      apply (rule allI)
    proof
      fix x
      assume assum3 : "x \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}"
      have "\<not> occursvari f 0 \<Longrightarrow> S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<Longrightarrow> x \<in> S' \<inter> {s. \<nexists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A} \<Longrightarrow> \<exists>s' act. act \<in> A \<and> (x, act, s') \<in> transition M \<and> s' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A}" using invariant by (simp)
      thus "\<exists>s'' act. act \<in> A \<and> (x, act, s'') \<in> (transition M) \<and> s'' \<in> S' \<inter> {s'. \<nexists>p s''. validfinpath M s' p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)}" using assum1 assum3 assms(1) by simp
    qed
    moreover have "s \<in> ?S'" using assum1 assum2 by auto
    ultimately show "s \<in> ?S' \<and> (\<forall>s'. (s' \<in> ?S' \<longrightarrow> (\<exists>s'' act. act \<in> A \<and> (s', act, s'') \<in> (transition M) \<and> s'' \<in> ?S')))" by auto
  qed
  thus ?thesis by auto
qed
 
lemma theorem21generalizedrtl : 
  assumes "\<not>(occursvari f 0)"
  and "finite A"
  and "((\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or>
     (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))" 
  shows "(s \<in> formulasemantics (nu (or f (Diamond A (var 0)))) M e)"
  apply (simp add: Diamond_eq_exist assms(2) newenvironment.cases)
proof-
  {
    assume "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)"
    from this obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)" by auto
    let ?S' = "{s. (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A))}"
    have "s \<in> ?S'" using assum1 by auto
    (*maybe generalize this and and set shiftdown f 0 M e to some set*)
    moreover have "?S' \<subseteq> (\<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'})"
    proof
      fix s
      assume "s \<in> {s. \<exists>p s'. validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A}"
      from this obtain p s' where assum1 : "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A" by auto
      have "validfinpath M s p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A \<Longrightarrow> s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and>  (\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> set (map action p) \<subseteq> A))"
        apply (induct p arbitrary : s)
        apply (simp_all add: validfinpath.cases)
      proof-
        fix t p
        (*assum2 only needed for base case*)
        assume assum3 : "t \<in> transition M \<and> validfinpath M (target t) p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action t \<in> A \<and> action ` set p \<subseteq> A"
        hence "(source t, action t, target t) \<in> transition M \<and> (validfinpath M (target t) p s' \<and> s' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action t \<in> A \<and> action ` set p \<subseteq> A)" using split by metis
        thus "source t \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (source t, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A))" by auto
      qed
      thus "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" using assum1 by auto
    qed
    ultimately have "?S' \<subseteq> (\<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}) \<and> s \<in> ?S'" by auto
  }
  moreover {
    assume "\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)"
    from this obtain p where assum1 : "validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)" by auto
    let ?S' = "{s. (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))}"
    have "s \<in> ?S'" using assum1 by auto
    moreover have "?S' \<subseteq> (\<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'})"
    proof
      fix s
      assume "s \<in> {s. (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A))}"
      from this obtain p where assum1 : "validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)" by auto
      hence "s = source (p 0) \<and> (p 0) \<in> transition M \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by (simp add: validinfpath_def)
      hence "(s, action (p 0), target (p 0)) \<in> transition M  \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by (simp add: source_def action_def target_def)
      hence "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and>  (\<exists>p. validinfpath M s' p \<and> (\<forall>n. action (p n) \<in> A))" by blast
      thus "s \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}" using assum1 by auto
    qed
    ultimately have "?S' \<subseteq> (\<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'}) \<and> s \<in> ?S'" by auto
  }
  ultimately have "\<exists>S'. S' \<subseteq> (\<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<and> s \<in> S'" using assms(3) by blast
  from this obtain S' where assum1 : "S' \<subseteq> (\<lbrakk>shiftdown f 0\<rbrakk> M e \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<and> s \<in> S'" by auto
  have "\<lbrakk>shiftdown f 0\<rbrakk> M e = \<lbrakk>f\<rbrakk> M (newenvironment e S')" using shiftdowncoro assms(1) by metis
  hence "S' \<subseteq> (\<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<and> s \<in> S'" using assum1 by auto
  thus "\<exists>S'. S' \<subseteq> (\<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}) \<and> s \<in> S'" by auto 
qed

lemma theorem21generalized :  
  assumes "\<not>(occursvari f 0)"
  and "finite A"
  shows "(s \<in> \<lbrakk>nu (or f (Diamond A (var 0)))\<rbrakk> M e) =
  ((\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or> 
  (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))"
  apply (rule iffI)
  using assms theorem21generalizedltr apply metis
  using assms theorem21generalizedrtl apply metis
  done

lemma Boxcomplement_locked : "finite (-B) \<Longrightarrow> (s \<in> \<lbrakk>Box (-B) ff\<rbrakk> M e = locked M B s)"
  apply (simp add : Box_eq_forall locked_def enabledactions_def)
  apply (blast)
  done
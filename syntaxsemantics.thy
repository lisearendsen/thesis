theory syntaxsemantics
imports Main
begin

datatype 'a regularformula =
  eps | acts "'a set" |
  after "'a regularformula" "'a regularformula"| 
  union "'a regularformula" "'a regularformula" | 
  repeat "'a regularformula"

text \<open>A regular formula is finite if and only if all sets of actions occurring in the 
formula are finite.\<close>

fun finitereg :: "'a regularformula \<Rightarrow> bool" where
"finitereg eps = True" |
"finitereg (acts A) = finite A" |
"finitereg (after R Q) = (finitereg R \<and> finitereg Q)" |
"finitereg (union R Q) = (finitereg R \<and> finitereg Q)" |
"finitereg (repeat R) = finitereg R"

(* from "HOL-Library.Regular-Sets.Regular_Exp" *)
definition conc :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr \<open>@@\<close> 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

(*this is probably also defined already*)
lemma conclem : "a \<in> A \<and> b \<in> B \<Longrightarrow> a@b \<in> A@@B"
  using conc_def by fastforce

lemma conclem' : "(ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> a \<in> A \<and> b \<in> B)"
  by (simp add: conc_def)

lemma conclem'' : "(map f ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> (map f a) \<in> A \<and> (map f b) \<in> B)"
  apply (rule iffI)
  apply (metis conclem' append_eq_map_conv)
  apply (metis conclem map_append)
  done

text \<open>Define powers on regular formulas to describe the language of the repeat operator.\<close>

overloading
  formpow \<equiv> "compow :: nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
begin
  fun formpow :: "nat \<Rightarrow>'a list set \<Rightarrow> 'a list set"
  where
    "formpow 0 A = {[]}" |
    "formpow (Suc n) A = A @@ (formpow n A)"
end

definition formpow :: "nat \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  formpow [code_abbrev]: "formpow = compow"

text \<open>Now the language of a regular formula can be defined.\<close>

fun regformtolanguage :: "'a regularformula \<Rightarrow> 'a list set" where
"regformtolanguage eps = {[]}" |
"regformtolanguage (acts A) = {[a] |a. (a \<in>A)}" |
"regformtolanguage (after R Q) = ({r @ q |r q. (r \<in> regformtolanguage R) \<and> (q \<in> regformtolanguage Q)})" |
"regformtolanguage (union R Q) = (regformtolanguage R) \<union> (regformtolanguage Q)" |
"regformtolanguage (repeat R) = (\<Union>n. (regformtolanguage R) ^^ n)"

value "regformtolanguage (eps) :: nat list set" 
value "regformtolanguage (acts {}) :: nat list set" 
value "regformtolanguage (after (acts {1, 2}) (acts {3, 4})) :: nat list set"

text \<open>A mu calculus formula is defined on a type of actions \<open>'a\<close>,
and de Bruijn indices are used as variables.\<close>

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

text \<open>Similarly a labeled transition system is defined on a type of actions \<open>'a\<close> 
and a type of states \<open>'s\<close> (instead of a set of actions and a set of states).
A labeled transition system then consists of a set of transitions and a set of initial states.\<close>

(*maybe remove set of initial states*)
record ('a, 's) lts =
transition :: "('s * 'a * 's) set"
initial :: "'s set"

datatype example_states = s\<^sub>0 | s\<^sub>1
datatype example_actions = \<a> | \<b>

text \<open>A record can be instantiated as follows.\<close>

definition example_lts :: "(example_actions, example_states) lts" where
"example_lts \<equiv> \<lparr>transition = {(s\<^sub>0, \<b>, s\<^sub>1), (s\<^sub>1, \<a>, s\<^sub>0), (s\<^sub>1, \<a>, s\<^sub>1)}, initial = {s\<^sub>0}\<rparr>"

fun newenvironment :: "(nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's set) " where
"newenvironment e S 0 = S" |
"newenvironment e S (Suc n) = e n"

text \<open>Some simplifications for \<open>newenvironment\<close>.\<close>

lemma newenvironmentsuccessorcomplement [simp] : 
"(newenvironment e S)((Suc i) := - ((newenvironment e S) (Suc i))) = newenvironment (e(i := - e i)) S"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentzerocomplement [simp] : 
"(newenvironment e S)(0 := (-(newenvironment e S) 0)) = (newenvironment e (-S))"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentswitchsuccessor [simp] : 
"newenvironment (e(i :=  S')) S'' = (newenvironment e S'')((Suc i) := S')"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentswitchzero [simp] : 
"(newenvironment e S'')(0 := S') = newenvironment e S'"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentshift [simp] : 
"X > 0 \<longrightarrow> (newenvironment e S') X = e (X - Suc 0)" by (induct_tac X; simp)

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

text \<open>Proving formulas on the example as given before.\<close>

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
  "(shiftup (diamond act f) i) = diamond act (shiftup f i)" |
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

fun Andlist :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula " where
"Andlist [] F = tt" |
"Andlist (a # as) F = and' (F a) (Andlist as F)"

definition And :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" where
"And A F = Andlist (if finite A then (SOME listA. set listA = A) else undefined) F"

lemma Andlist_eq_all : "\<lbrakk>Andlist Alist F\<rbrakk> M e = {s. \<forall>a \<in> set Alist. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  by (induct Alist; simp; auto)

lemma And_eq_all : "finite A \<Longrightarrow> \<lbrakk>And A F\<rbrakk> M e = {s. \<forall>a \<in> A. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  apply (simp add: And_def Andlist_eq_all)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma And_eq_all' [simp] : "finite A \<Longrightarrow> \<lbrakk>And A F\<rbrakk> M e = (\<Inter>a \<in> A. {s. s \<in> \<lbrakk>F a\<rbrakk> M e})"
  by (subst And_eq_all; simp; auto)

fun Orlist :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula " where
"Orlist [] F = ff" |
"Orlist (a # as) F = or (F a) (Orlist as F)"

definition Or :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a formula) \<Rightarrow> 'a formula" where
"Or A F = Orlist (if finite A then (SOME listA. set listA = A) else undefined) F"

lemma Orlist_eq_exist : "\<lbrakk>Orlist Alist F\<rbrakk> M e = {s. \<exists>a \<in> set Alist. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  by (induct Alist; auto)

lemma Or_eq_exist : "finite A \<Longrightarrow> \<lbrakk>Or A F\<rbrakk> M e = {s. \<exists>a \<in> A. s \<in> \<lbrakk>F a\<rbrakk> M e}"
  apply (simp add: Or_def Orlist_eq_exist)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma Or_eq_all' : "finite A \<Longrightarrow> \<lbrakk>Or A F\<rbrakk> M e = (\<Union>a \<in> A. {s. s \<in> \<lbrakk>F a\<rbrakk> M e})"
  by (subst Or_eq_exist; auto)

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

lemma Diamond_eq_exist [simp] : "finite A \<Longrightarrow>
\<lbrakk>Diamond (acts A) f\<rbrakk> M e = {s. \<exists> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Diamondlist_eq_exist)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma shiftuptwice : "m \<le> i \<Longrightarrow> shiftup (shiftup f m) (Suc i) = shiftup (shiftup f i) m"
  by (induct f arbitrary : i m; simp)

lemma shiftupDiamondlist [simp] : "shiftup (Diamondlist Alist f) i = Diamondlist Alist (shiftup f i)"
  by (induct Alist; simp)

lemma shiftupDiamond [simp] : "finitereg R \<Longrightarrow> shiftup (Diamond R f) i = Diamond R (shiftup f i)"
  by (induction R arbitrary : i f; simp add: shiftuptwice)

lemma shiftupdown : "m \<le> i \<Longrightarrow> shiftdown (shiftup f m) (Suc i) = shiftup (shiftdown f i) m"
  by (induct f arbitrary : i m; simp; arith)

lemma shiftdownDiamondlist [simp] : "shiftdown (Diamondlist Alist f) i = Diamondlist Alist (shiftdown f i)"
  by (induct Alist; simp)

lemma shiftdownDiamond [simp] : "finitereg R \<Longrightarrow> shiftdown (Diamond R f) i = Diamond R (shiftdown f i)"
  by (induction R arbitrary : i f; simp add: shiftupdown)

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

lemma shiftupBoxlist [simp] : "shiftup (Boxlist Alist f) i = Boxlist Alist (shiftup f i)"
  by (induct Alist; simp)

lemma shiftupBox : "finitereg R \<Longrightarrow> shiftup (Box R f) i = Box R (shiftup f i)"
  by (induction R arbitrary : i f; simp add: shiftuptwice)

lemma shiftdownBoxlist [simp] : "shiftdown (Boxlist Alist f) i = Boxlist Alist (shiftdown f i)"
  by (induct Alist; simp)

lemma shiftdownBox [simp] : "finitereg R \<Longrightarrow> shiftdown (Box R f) i = Box R (shiftdown f i)"
  by (induction R arbitrary : i f; simp add: shiftupdown)

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

lemma negvarishiftup : "m \<le> i \<Longrightarrow> negvari (shiftup f m) (Suc i) = shiftup (negvari f i) m"
  by (induct f arbitrary : m i; simp)

lemma negvariDiamondlist [simp] : "negvari (Diamondlist Alist f) i = Diamondlist Alist (negvari f i)"
  by (induct Alist; simp)

lemma negvariDiamond [simp] : "finitereg R \<Longrightarrow> negvari (Diamond R f) i = Diamond R (negvari f i)"
  by (induct R arbitrary : f i; simp add : negvarishiftup)

lemma negvariBoxlist [simp] : "negvari (Boxlist Alist f) i = Boxlist Alist (negvari f i)"
  by (induct Alist; simp)

lemma negvariBox [simp] : "finitereg R \<Longrightarrow> negvari (Box R f) i = Box R (negvari f i)"
  by (induct R arbitrary : f i; simp add : negvarishiftup)

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

fun emptyreg :: "'a regularformula \<Rightarrow> bool" where
  "emptyreg eps = False" | 
  "emptyreg (acts A) = (A = {})" |
  "emptyreg (after R Q) = (emptyreg R \<or> emptyreg Q)" |
  "emptyreg (union R Q) = (emptyreg R \<and> emptyreg Q)" | 
  "emptyreg (repeat R) = False"

lemma occursvarishiftup : "m \<le> i \<Longrightarrow> occursvari (shiftup f m) (Suc i) = occursvari f i"
  by (induct f arbitrary : i m; simp)

lemma occursDiamondlist [simp] : "occursvari (Diamondlist Alist f) i = (occursvari f i \<and> \<not>(Alist = []))"
  by (induct Alist arbitrary : f i; simp; blast)

lemma occursDiamond [simp] : "finitereg R \<Longrightarrow> (occursvari (Diamond R f) i) = (occursvari f i \<and> \<not>emptyreg R)"
  apply (induct R arbitrary : f i; simp add : occursvarishiftup)
  apply (rule someI2_ex)
  apply (simp add: finite_list)
  apply (blast)
  apply (blast)
  apply (blast)
  done

lemma occursBoxlist [simp] : "occursvari (Boxlist Alist f) i = (occursvari f i \<and> \<not>(Alist = []))"
  by (induct Alist arbitrary : f i; simp; blast)

lemma occursBox [simp] : "finitereg R \<Longrightarrow> (occursvari (Box R f) i) = (occursvari f i \<and> \<not>emptyreg R)"
  apply (induct R arbitrary : f i; simp add : occursvarishiftup)
  apply (rule someI2_ex)
  apply (simp add: finite_list)
  apply (blast)
  apply (blast)
  apply (blast)
  done

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
  mono (\<lambda>S.(\<lbrakk>f\<rbrakk> M (e(i := S)))) \<and> antimono (\<lambda>S.(\<lbrakk>f\<rbrakk> M (e(i := S))))"
  by (induct f arbitrary: i; simp add: dependvari_def monotone_def)

lemma notdependscoro : "(\<not>dependvari f M 0 \<longrightarrow> mono (transformer f M e))"
  apply (simp add: transformerdef)
proof-
  have "\<forall>S''. \<not>dependvari f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using notdependsmono by metis
  thus "\<not>dependvari f M 0 \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

lemma andsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<and> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>1 \<and> A\<^sub>1 \<inter> A\<^sub>2 \<subseteq> B\<^sub>2"
  using assms by auto

lemma orsubset : 
  assumes "A\<^sub>1 \<subseteq> B\<^sub>1 \<or> A\<^sub>2 \<subseteq> B\<^sub>2"
  shows "A\<^sub>1 \<subseteq> B\<^sub>1 \<union> B\<^sub>2 \<or> A\<^sub>2 \<subseteq> B\<^sub>1 \<union> B\<^sub>2"
  using assms by auto

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

fun notdependalloccursposnegi :: "'a formula \<Rightarrow> ('a ,'s) lts \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool"
where 
  "(notdependalloccursposnegi tt M i b) = True " |
  "(notdependalloccursposnegi ff M i b) = True" |
  "(notdependalloccursposnegi (var X) M i b) = ((X \<noteq> i) \<or> b)" |
  "(notdependalloccursposnegi (neg f) M i b) = (\<not>dependvari f M i \<or> notdependalloccursposnegi f M i (\<not>b))" |
  "(notdependalloccursposnegi (and' f f') M i b) = (\<not>dependvari (and' f f') M i \<or> (notdependalloccursposnegi f M i b \<and> notdependalloccursposnegi f' M i b))" |
  "(notdependalloccursposnegi (or f f') M i b) = (\<not>dependvari (or f f') M i \<or> (notdependalloccursposnegi f M i b \<and> notdependalloccursposnegi f' M i b))" |
  "(notdependalloccursposnegi (diamond act f) M i b) = (\<not>dependvari (diamond act f) M i \<or> notdependalloccursposnegi f M i b) " |
  "(notdependalloccursposnegi (box act f) M i b) = (\<not>dependvari (box act f) M i \<or> notdependalloccursposnegi f M i b)" |
  "(notdependalloccursposnegi (nu f) M i b) = (\<not>dependvari (nu f) M i \<or> notdependalloccursposnegi f M (Suc i) b)" |
  "(notdependalloccursposnegi (mu f) M i b) = (\<not>dependvari (mu f) M i \<or> notdependalloccursposnegi f M (Suc i) b)"

lemma alloccursposnegnotdepends : "alloccursposnegi f i b \<Longrightarrow> notdependalloccursposnegi f M i b"
  by (induct f arbitrary : i b; simp)

lemma dependvarineg : "dependvari f M i = dependvari (neg f) M i"
  by (simp add: dependvari_def)

lemma notdepends : "\<not>dependvari f M i \<Longrightarrow> notdependalloccursposnegi f M i b"
  apply (induct f arbitrary : i b; simp add: dependvari_def)
  apply (rule impI)
  apply (subgoal_tac "({} :: 's set) = UNIV")
  apply auto
  done

lemma monotonicitynotdepend :
"(notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'.(formulasemantics f M (e(i := S')))))
 \<and> (notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'.(formulasemantics f M (e(i := S')))))"
  (*apply (simp add: monotone_def)*)
  apply (induct f arbitrary : i e)
        prefer 4
        unfolding notdependalloccursposnegi.simps
        apply (subst dependvarineg)
        apply (simp add: monotone_def dependvari_def)
                prefer 6

  unfolding notdependalloccursposnegi.simps
  apply auto
           apply (meti notdependsmono monotone_def alloccursposnegi.simps(8) boxsubset)
  unfolding notdependalloccursposnegi.simps
  apply (subst boxsubset)
  (*apply (metis boxsubset dependvari_def equalityE
      notdependalloccursposnegi.simps(8))
  apply (meson alloccursposnegi.simps(8) boxsubset)
  apply (induction f arbitrary : i e)
  apply (simp_all add: monotone_def)*)
proof-

end
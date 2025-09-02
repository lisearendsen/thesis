theory syntaxsemantics
imports Main "Regular-Sets.Regular_Exp" "HOL-Library.Omega_Words_Fun"
begin

text \<open>We extend \<open>rexp\<close> by adding a constructor \<open>Acts\<close>, representing a set of actions.
In this way regular expressions are inherently finite\<close>

fun Actslist :: "'a list \<Rightarrow> 'a rexp " where
"Actslist [] = Zero" |
"Actslist (a # as) = Plus (Actslist as) (Atom a)"

definition Acts :: "'a set \<Rightarrow> 'a rexp" where
"Acts A = Actslist (if finite A then (SOME listA. set listA = A) else undefined)"

lemma Actslistlang : "lang (Actslist A) =  {[a] |a. a \<in> set A}"
  by (induct A; auto)

lemma Actslang [simp] : "finite A \<Longrightarrow> lang (Acts A) =  {[a] |a. a \<in> A}"
  apply (simp add: Acts_def Actslistlang)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma abinconc : "a \<in> A \<and> b \<in> B \<Longrightarrow> a@b \<in> A@@B"
  using concat_def by blast

lemma exists_abinconc : "(ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> a \<in> A \<and> b \<in> B)"
  by blast

lemma exists_map_abinconc : "(map f ab \<in> A@@B) = (\<exists>a b. ab = a@b \<and> (map f a) \<in> A \<and> (map f b) \<in> B)"
  apply (rule iffI)
  apply (metis exists_abinconc append_eq_map_conv)
  apply (metis abinconc map_append)
  done

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
transition :: "('s \<times> 'a \<times> 's) set"
initial :: "'s set"

datatype example_states = s\<^sub>0 | s\<^sub>1
datatype example_actions = \<a> | \<b>

text \<open>A record can be instantiated as follows.\<close>

definition example_lts :: "(example_actions, example_states) lts" where
"example_lts \<equiv> \<lparr>transition = {(s\<^sub>0, \<b>, s\<^sub>1), (s\<^sub>1, \<a>, s\<^sub>0), (s\<^sub>1, \<a>, s\<^sub>1)}, initial = {s\<^sub>0}\<rparr>"

abbreviation newenvironment :: "(nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> (nat \<Rightarrow> 's set) " where
"newenvironment e S' \<equiv> S' ## e"

text \<open>Some simplifications for \<open>newenvironment\<close>, specifically with respect to updating the environment.\<close>

lemma newenvironmentsuccessorcomplement [simp] : 
"(newenvironment e S')((Suc i) := - ((newenvironment e S') (Suc i))) = newenvironment (e(i := - e i)) S'"
  apply (rule)
  apply (induct_tac x; simp)
  done

lemma newenvironmentzerocomplement [simp] : 
"(newenvironment e S')(0 := (-(newenvironment e S') 0)) = newenvironment e (-S')"
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

text \<open>Proving semantics of formulas on the example as given before.\<close>

lemma "\<lbrakk>box \<a> ff\<rbrakk> example_lts e = {s\<^sub>0}"
  apply (simp add: example_lts_def)
  using example_states.exhaust apply auto
  done

lemma "\<lbrakk>nu (diamond \<a> (var 0))\<rbrakk> example_lts e = {s\<^sub>1}"
proof-
  have "\<forall>S'. S' \<subseteq> {s. \<exists>s'. ((s = s\<^sub>1 \<and> s' = s\<^sub>0) \<or> (s = s\<^sub>1 \<and> s' = s\<^sub>1)) \<and> s' \<in> S'} = (S' = {} \<or> S' = {s\<^sub>1})" using example_states.exhaust by auto
  hence "\<Union> {S'. S' \<subseteq> {s. \<exists>s'. ((s = s\<^sub>1 \<and> s' = s\<^sub>0) \<or> (s = s\<^sub>1 \<and> s' = s\<^sub>1)) \<and> s' \<in> S'}} = {s\<^sub>1}" by auto
  thus ?thesis by (simp add: example_lts_def)
qed

lemma "\<lbrakk>nu (diamond \<a> (var 0))\<rbrakk> example_lts e = {s\<^sub>1}"
  apply (simp add: example_lts_def)
  apply (rule equalityI)
  apply blast
  apply (rule Union_upper)
  apply auto
  done

text \<open>\<open>shiftup\<close> is defined on formulas to be able to wrap a formula in a new binder 
without changing its definition. For example, \<open>var 0\<close> and \<open>mu (var 1)\<close> represent the same formula.
\<open>shiftdown\<close> is its opposite.\<close>

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

text \<open>Defining extensions of the mu calculus, specifically \<open>And\<close>, \<open>Or\<close>, \<open>Diamond\<close>, and \<open>Box\<close>.\<close>

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
  by (subst And_eq_all; auto)

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

lemma Or_eq_exist' : "finite A \<Longrightarrow> \<lbrakk>Or A F\<rbrakk> M e = (\<Union>a \<in> A. {s. s \<in> \<lbrakk>F a\<rbrakk> M e})"
  by (subst Or_eq_exist; auto)

fun Diamond :: "'a rexp \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where 
"Diamond Zero f = ff" |
"Diamond One f = f" |
"Diamond (Atom a) f = diamond a f" |
"Diamond (Plus R Q) f = or (Diamond R f) (Diamond Q f)" |
"Diamond (Times R Q) f = Diamond R (Diamond Q f)" |
"Diamond (Star R) f =  mu (or (Diamond R (var 0)) (shiftup f 0))" 

lemma Diamondlist_eq_exist [simp] : 
"\<lbrakk>Diamond (Actslist A) f\<rbrakk> M e = {s. \<exists> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; auto)

lemma Diamond_eq_exist [simp] : "finite A \<Longrightarrow>
\<lbrakk>Diamond (Acts A) f\<rbrakk> M e = {s. \<exists> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Acts_def)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma shiftuptwice : "m \<le> i \<Longrightarrow> shiftup (shiftup f m) (Suc i) = shiftup (shiftup f i) m"
  by (induct f arbitrary : i m; simp)

lemma shiftupDiamond [simp] : "shiftup (Diamond R f) i = Diamond R (shiftup f i)"
  by (induct R arbitrary : i f; simp add: shiftuptwice)

lemma shiftupdown : "m \<le> i \<Longrightarrow> shiftdown (shiftup f m) (Suc i) = shiftup (shiftdown f i) m"
  by (induct f arbitrary : i m; simp; arith)

lemma shiftdownDiamond [simp] : "shiftdown (Diamond R f) i = Diamond R (shiftdown f i)"
  by (induct R arbitrary : i f; simp add: shiftupdown)

fun Box :: "'a rexp \<Rightarrow> 'a formula \<Rightarrow> 'a formula " where 
"Box Zero f = tt" |
"Box One f = f" |
"Box (Atom a) f = box a f" |
"Box (Plus R Q) f = and' (Box R f) (Box Q f)" |
"Box (Times R Q) f = Box R (Box Q f)" |
"Box (Star R) f =  nu (and' (Box R (var 0)) (shiftup f 0))" 

lemma Boxlist_eq_forall [simp] : "\<lbrakk>Box (Actslist A) f\<rbrakk> M e = {s. \<forall> s' act. act \<in> set A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  by (induct A; auto)

lemma Box_eq_forall [simp] : "finite A \<Longrightarrow>
\<lbrakk>Box (Acts A) f\<rbrakk> M e = {s. \<forall> s' act. act \<in> A \<and> (s, act, s') \<in> (transition M) \<longrightarrow> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  apply (simp add: Acts_def)
  apply (rule someI2_ex; simp add: finite_list)
  done

lemma shiftupBox [simp] : "shiftup (Box R f) i = Box R (shiftup f i)"
  by (induct R arbitrary : i f; simp add: shiftuptwice)

lemma shiftdownBox [simp] : "shiftdown (Box R f) i = Box R (shiftdown f i)"
  by (induct R arbitrary : i f; simp add: shiftupdown)

text \<open>Defining \<open>negvari\<close> to prove duality of mu and nu, and also proving definition on our extensions.\<close>

fun negvari :: "'a formula \<Rightarrow> nat \<Rightarrow> 'a formula "
where 
  "negvari tt i = tt " |
  "negvari ff i = ff" |
  "negvari (var X) i  = (if i = X then neg (var X) else var X)" |
  "negvari (neg f) i = neg (negvari f i)" |
  "negvari (and' f f') i = and' (negvari f i) (negvari f' i) " |
  "negvari (or f f') i = or (negvari f i) (negvari f' i)" |
  "negvari (diamond a f) i = diamond a (negvari f i) " |
  "negvari (box a f) i = box a (negvari f i)" |
  "negvari (nu f) i = nu (negvari f (Suc i))" |
  "negvari (mu f) i = mu (negvari f (Suc i))"

lemma negvarishiftup : "m \<le> i \<Longrightarrow> negvari (shiftup f m) (Suc i) = shiftup (negvari f i) m"
  by (induct f arbitrary : m i; simp)

lemma negvariDiamond [simp] : "negvari (Diamond R f) i = Diamond R (negvari f i)"
  by (induct R arbitrary : f i; simp add : negvarishiftup)

lemma negvariBox [simp] : "negvari (Box R f) i = Box R (negvari f i)"
  by (induct R arbitrary : f i; simp add : negvarishiftup)

value "negvari (or (var 0) (mu (and' (var 0) (var 1)))) 0 :: nat formula"

section \<open>Proving duality of formulas.\<close>

lemma negtrue [simp] : "\<lbrakk>neg tt\<rbrakk> M e = \<lbrakk>ff\<rbrakk> M e"
  by simp

lemma negfalse [simp]: "\<lbrakk>neg ff\<rbrakk> M e = \<lbrakk>tt\<rbrakk> M e"
  by simp

lemma negnegf [simp] : "\<lbrakk>neg (neg (f))\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  by simp

lemma negand' [simp] : "\<lbrakk>neg (and' f f')\<rbrakk> M e = \<lbrakk>or (neg f) (neg f')\<rbrakk> M e"
  by simp

lemma negor [simp] : "\<lbrakk>neg (or f f')\<rbrakk> M e = \<lbrakk>and' (neg f) (neg f')\<rbrakk> M e"
  by simp

lemma negbox : "\<lbrakk>neg (box act f)\<rbrakk> M e = \<lbrakk>diamond act (neg f)\<rbrakk> M e"
  by auto

lemma negdiamond : "\<lbrakk>neg (diamond act f)\<rbrakk> M e = \<lbrakk>box act (neg f)\<rbrakk> M e"
  by auto

lemma movenegvariin : "\<lbrakk>f\<rbrakk> M (e(i := -e(i))) = \<lbrakk>negvari f i\<rbrakk> M e"
  apply (induct f arbitrary : e i; simp; subgoal_tac "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := - e i) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')")
  apply simp_all
proof-
  fix f e i S'
  assume "\<And>e i. \<lbrakk>f\<rbrakk> M e(i := - e i) = \<lbrakk>negvari f i\<rbrakk> M e"
  hence "\<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := - (newenvironment e S' (Suc i)))) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')" by metis
  moreover have "\<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := - (newenvironment e S' (Suc i)))) = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (Suc i := - e i))" by simp
  ultimately show "\<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := - e i) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')" by simp
  thus " \<lbrakk>f\<rbrakk> M (newenvironment e S') (Suc i := - e i) = \<lbrakk>negvari f (Suc i)\<rbrakk> M (newenvironment e S')" by simp
qed

lemma pushnegnu : "\<lbrakk>neg (nu f)\<rbrakk> M e = \<Inter> {S. S \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S))}"
proof-
  have "- \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')} = \<Inter> {-S'| S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by blast
  moreover have "... = \<Inter> {S'. -S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e (-S'))}" using double_compl by metis
  moreover have "... = \<Inter> {S. S \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S))}" by auto
  ultimately show ?thesis by simp
qed

lemma negnu : "\<lbrakk>neg (nu f)\<rbrakk> M e = \<lbrakk>mu (neg (negvari f 0))\<rbrakk> M e"
proof-
  have "\<And> S'. \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S')) = \<lbrakk>negvari (neg f) 0\<rbrakk> M (newenvironment e S')" using movenegvariin newenvironmentzerocomplement by metis  
  hence "\<Inter> {S'. S' \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S'))} = \<Inter> {S'. S' \<supseteq> \<lbrakk>neg (negvari f 0)\<rbrakk> M (newenvironment e S')}" by auto
  moreover have "\<lbrakk>neg (nu f)\<rbrakk> M e = (\<Inter> {S'. S' \<supseteq> \<lbrakk>neg f\<rbrakk> M (newenvironment e (-S'))})" using pushnegnu by metis
  ultimately show ?thesis by auto
qed  

lemma negvarnegvar [simp] : "\<lbrakk>negvari (negvari f i) i\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  (*by (metis (mono_tags, opaque_lifting)
      boolean_algebra_class.boolean_algebra.double_compl fun_upd_def fun_upd_triv
      fun_upd_upd movenegvariin)*)
  by (induct f arbitrary : i e; simp)

lemma negmu : "\<lbrakk>neg (mu f)\<rbrakk> M e = \<lbrakk>nu (neg (negvari f 0))\<rbrakk> M e"
proof-
  have "\<lbrakk>mu (neg (negvari (neg (negvari f 0)) 0))\<rbrakk> M e = \<lbrakk>neg (nu (neg (negvari f 0)))\<rbrakk> M e" by (simp only: negnu)
  hence "\<lbrakk>neg (mu (neg (negvari (neg (negvari f 0)) 0)))\<rbrakk> M e = \<lbrakk>neg (neg (nu (neg (negvari f 0))))\<rbrakk> M e" by auto
  thus ?thesis by simp
qed

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

lemma closedformula : "((\<forall>i \<ge> j. \<not>occursvari f i) \<and> (\<forall>i < j. e i = e' i)) \<longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e'"
  apply (induct f arbitrary: e e' j; simp)
  using linorder_le_less_linear apply blast
  apply blast
  apply blast
  apply (rule impI; subgoal_tac "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')")
  apply simp
  prefer 2 
  apply (rule impI; subgoal_tac "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')")
  apply simp
proof-
  fix f j
  fix e e' :: "nat \<Rightarrow> 'b set"
  fix S' :: "'b set"
  assume "(\<And>e e' j. (\<forall>i\<ge>j. \<not> occursvari f i) \<and> (\<forall>i<j. e i = e' i) \<longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e')"
  moreover {
    assume "\<forall>i\<ge>j. \<not> occursvari f (Suc i)"
    hence "\<forall>i \<ge> Suc j. \<not> occursvari f i" using Suc_le_D by auto 
  }
  moreover {
    assume assum1 : "\<forall>i<j. e i = e' i"
    have "\<forall>i<Suc j. newenvironment e S' i = newenvironment e' S' i" 
      by (rule; induct_tac i; simp add: assum1)
  }
  moreover assume "(\<forall>i\<ge>j. \<not> occursvari f (Suc i)) \<and> (\<forall>i<j. e i = e' i)"
  ultimately show "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')" by auto
  thus "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M (newenvironment e' S')" by simp
qed

lemma closedformulacoro : "(\<And>i. \<not>occursvari f i) \<Longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e'"
  using closedformula less_nat_zero_code by metis

fun emptyreg :: "'a rexp \<Rightarrow> bool" where
  "emptyreg Zero = True" | 
  "emptyreg One = False" | 
  "emptyreg (Atom a) = False" |
  "emptyreg (Plus R Q) = (emptyreg R \<and> emptyreg Q)" |
  "emptyreg (Times R Q) = (emptyreg R \<or> emptyreg Q)" | 
  "emptyreg (Star R) = False"

lemma emptyregdef : "emptyreg R = (lang R = {})"
  by (induct R; auto)

lemma occursvarishiftup : "m \<le> i \<Longrightarrow> occursvari (shiftup f m) (Suc i) = occursvari f i"
  by (induct f arbitrary : i m; simp)

lemma occursDiamond [simp] : "(occursvari (Diamond R f) i) = (occursvari f i \<and> \<not>emptyreg R)"
  by (induct R arbitrary : f i; simp add : occursvarishiftup; auto)

lemma occursBox [simp] : "(occursvari (Box R f) i) = (occursvari f i \<and> \<not>emptyreg R)"
  by (induct R arbitrary : f i; simp add : occursvarishiftup; auto)

definition transformer :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's set "
  where
"transformer f M e S' = \<lbrakk>f\<rbrakk> M (newenvironment e S')"

lemma transformerdef : "transformer f M e = (\<lambda>S'. \<lbrakk>f\<rbrakk> M (newenvironment e S'))"
  by (rule; simp add: transformer_def)

definition dependvari :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> nat \<Rightarrow> bool" where
"dependvari f M i = (\<exists>e S'. \<lbrakk>f\<rbrakk> M e \<noteq> \<lbrakk>f\<rbrakk> M (e(i := S')))"

lemma dependvarX : "dependvari (var X) M i = (X = i)"
  by (auto simp: dependvari_def)

lemma dependvarineg : "dependvari (neg f) M i = dependvari f M i"
  by (simp add: dependvari_def)

lemma dependvariandor : "\<not>dependvari f1 M i \<and> \<not>dependvari f2 M i \<Longrightarrow> \<not>dependvari (and' f1 f2) M i \<and> \<not>dependvari (or f1 f2) M i"
  by (simp add: dependvari_def)

lemma dependvariboxdiamond : "\<not>dependvari f M i  \<Longrightarrow> \<not>dependvari (box a f) M i \<and> \<not>dependvari (diamond a f) M i"
  by (simp add: dependvari_def)

lemma dependvarinumu : "\<not>dependvari f M (Suc i)  \<Longrightarrow> \<not>dependvari (nu f) M i \<and> \<not>dependvari (mu f) M i"
  by (simp add: dependvari_def)

lemma notoccursnotdepends : "\<not>occursvari f i \<longrightarrow> \<not>dependvari f M i"
  apply (induct f arbitrary: i; simp add: dependvarineg dependvariandor dependvariboxdiamond dependvarinumu)
  apply (simp_all add: dependvari_def)
  done

lemma dependsoccurs : "dependvari f M i \<Longrightarrow> occursvari f i"
  using notoccursnotdepends by auto

lemma concsubst : "length e = Suc i \<Longrightarrow> (conc (take i e) (S' ## env)) (i := e!i) = conc e env" 
proof
  fix j
  assume assum1: "length e = Suc i"
  have "j < i \<or> j = i \<or> j \<ge> Suc i" by auto
  moreover {
    assume "j < i"
    hence "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" using assum1 by auto
  }
  moreover {
    assume "j = i"
    hence "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" using assum1 by auto
  }
  moreover {
    assume "j \<ge> Suc i"
    hence "j - i = Suc (j - Suc i)" by auto
    hence "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" using assum1 by auto
  }
  ultimately show "((conc (take i e) (S' ## env)) (i := e ! i)) j = (conc e env) j" by auto
qed

lemma notdependfirstpart : "(\<forall>i < j. \<not>dependvari f M i) \<and> (length e = length e' \<and> length e \<le> j)
    \<Longrightarrow> \<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)"
  apply (induct j arbitrary: e e' env)
  apply auto[1]
proof-
  fix j env
  fix e e' :: "'b set list"
  assume assum1 : "(\<And>e e' env. (\<forall>i<j. \<not> dependvari f M i) \<and> length e = length e' \<and> length e \<le> j \<Longrightarrow> \<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env))"
  assume assum2 : "(\<forall>i<Suc j. \<not> dependvari f M i) \<and> length e = length e' \<and> length e \<le> Suc j"
  hence " length e = Suc j \<or> length e \<le> j" by auto
  moreover {
    have "\<lbrakk>f\<rbrakk> M (conc (take j e) (env 0 ## env)) = \<lbrakk>f\<rbrakk> M (conc (take j e') (env 0 ## env))" by (simp add: assum1 assum2)
    hence "\<lbrakk>f\<rbrakk> M ((conc (take j e) (env 0 ## env)) (j := e!j)) = \<lbrakk>f\<rbrakk> M ((conc (take j e') (env 0 ## env)) (j := e'!j))" using assum2 by (simp add: dependvari_def)
    moreover assume "length e = Suc j"
    ultimately have "\<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)" using concsubst assum2 by metis 
  }
  moreover {
    assume "length e \<le> j"
    moreover have "(\<forall>i<j. \<not> dependvari f M i) \<and> length e = length e'" using assum2 by auto
    ultimately have "\<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)" using assum1 by metis
  }
  ultimately show "\<lbrakk>f\<rbrakk> M (conc e env) = \<lbrakk>f\<rbrakk> M (conc e' env)" by auto
qed

lemma existsmaxoccurs : "\<exists>j. \<forall>i \<ge> j. \<not>occursvari f i"
  apply (induct f; simp)
  using Suc_n_not_le_n apply blast
proof-
  fix f1 f2 :: "'a formula"
  assume "\<exists>j. \<forall>i\<ge>j. \<not> occursvari f1 i"
  moreover assume "\<exists>j. \<forall>i\<ge>j. \<not> occursvari f2 i"
  ultimately obtain j j' where "(\<forall>i\<ge>j. \<not> occursvari f1 i) \<and> (\<forall>i\<ge>j'. \<not> occursvari f2 i)" by auto
  hence "\<forall>i\<ge>(max j j'). \<not> occursvari f1 i \<and>  \<not> occursvari f2 i" by simp
  thus "\<exists>j. \<forall>i\<ge>j. \<not> occursvari f1 i \<and>  \<not> occursvari f2 i" by blast
  thus "\<exists>j. \<forall>i\<ge>j. \<not> occursvari f1 i \<and>  \<not> occursvari f2 i" by simp
next
  fix f :: "'a formula"
  assume "\<exists>j. \<forall>i\<ge>j. \<not> occursvari f i"
  from this obtain j where "\<forall>i\<ge>j. \<not> occursvari f i" by auto
  hence "\<forall>i\<ge>Suc j. \<not> occursvari f (Suc i)" by simp
  thus "\<exists>j. \<forall>i\<ge>j. \<not> occursvari f (Suc i)" by blast
  thus "\<exists>j. \<forall>i\<ge>j. \<not> occursvari f (Suc i)" by simp
qed

lemma notdependlastpart : "(\<forall>i\<ge>length elist. \<not>occursvari f i) \<longrightarrow> \<lbrakk>f\<rbrakk> M (conc elist e) = \<lbrakk>f\<rbrakk> M (conc elist e')"
  apply (induct f arbitrary : e e' elist; simp; rule impI)
  apply (subgoal_tac "x < length elist")
  apply simp
  apply arith
  apply blast
  apply blast
  apply blast
  apply blast
proof-
  fix f e e' 
  fix elist :: "'a set list"
  assume assum1: "(\<And>e e' elist. (\<forall>i\<ge>length elist. \<not> occursvari f i) \<longrightarrow> \<lbrakk>f\<rbrakk> M (elist \<frown> e) = \<lbrakk>f\<rbrakk> M (elist \<frown> e'))"
  assume "\<forall>i\<ge>length elist. \<not> occursvari f (Suc i)"
  hence "\<forall>i \<ge> Suc (length elist). \<not> occursvari f i" using Suc_le_D by auto
  moreover have "\<And>S'. length (S' # elist) = Suc (length elist)" by simp
  ultimately have conclusion : "\<And>S'. \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e) S') = \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e') S')" using assum1 build_cons by metis
  thus "\<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e) S')} = \<Union> {S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e') S')}" by auto
  thus "\<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e) S') \<subseteq> S'} = \<Inter> {S'. \<lbrakk>f\<rbrakk> M (newenvironment (conc elist e') S') \<subseteq> S'}" using conclusion by auto
qed

lemma notdependchangeenv : "(\<And>i. \<not>dependvari f M i) \<Longrightarrow> \<lbrakk>f\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e'"
proof-
  obtain j where assum1:"\<forall>i \<ge> j. \<not>occursvari f i" using existsmaxoccurs by auto
  assume "\<And>i. \<not>dependvari f M i"
  hence "\<forall>i<j. \<not>dependvari f M i" by auto
  moreover have "length (prefix j e) = length (prefix j e') \<and> length (prefix j e) \<le> j" by auto
  ultimately have res1: "\<lbrakk>f\<rbrakk> M (conc (prefix j e) (suffix j e)) = \<lbrakk>f\<rbrakk> M (conc (prefix j e') (suffix j e))" using notdependfirstpart by metis
  have "length (prefix j e') = j" by auto
  hence res2: "\<lbrakk>f\<rbrakk> M (conc (prefix j e') (suffix j e)) = \<lbrakk>f\<rbrakk> M (conc (prefix j e') (suffix j e'))" using assum1 notdependlastpart by metis
  show ?thesis using res1 res2 by auto
qed

lemma notdependseqnu :
  assumes "\<not> dependvari f M 0"
  shows "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>nu f\<rbrakk> M e"
proof-
  have "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (0 := S''))" using assms dependvari_def by blast
  hence "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') = \<lbrakk>f\<rbrakk> M (newenvironment e S')" by auto
  hence "\<Union> {S''. S'' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S'')} = \<Union> {S''. S'' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S')}" by blast
  thus ?thesis by auto
qed

lemma notdependseqmu :
  assumes "\<not> dependvari f M 0"
  shows "\<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>mu f\<rbrakk> M e"
proof-
  have "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M ((newenvironment e S') (0 := S''))" using assms dependvari_def by blast
  hence "\<forall>S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') = \<lbrakk>f\<rbrakk> M (newenvironment e S')" by auto
  hence "\<Inter> {S''. \<lbrakk>f\<rbrakk> M (newenvironment e S'') \<subseteq> S''} = \<Inter> {S''. \<lbrakk>f\<rbrakk> M (newenvironment e S') \<subseteq> S''}" by blast
  thus ?thesis by auto
qed

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

text \<open>Defining function \<open>notdependalloccursposnegi\<close> that can be evaluated on formulas and
proving that this evaluation can imply monotonicity (or antimonotonicity).\<close>

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

lemma notdepends : "\<not>dependvari f M i \<Longrightarrow> notdependalloccursposnegi f M i b"
  apply (induct f arbitrary : i b; simp add: dependvari_def)
  apply (rule impI)
  apply auto
  done

lemma andormono : 
  assumes "mono f1 \<and> mono f2"
  shows "mono (\<lambda>S'. f1 S' \<inter> f2 S')"
  and "mono (\<lambda>S'. f1 S' \<union> f2 S')"
  apply (simp_all add: monotone_def)
  apply (metis assms andsubset monotone_def)
  apply (metis assms orsubset monotone_def)
  done

lemma andorantimono : 
  assumes "antimono f1 \<and> antimono f2"
  shows "antimono (\<lambda>S'. f1 S' \<inter> f2 S')"
  and "antimono (\<lambda>S'. f1 S' \<union> f2 S')"
  apply (simp_all add: monotone_def)
  apply (metis assms andsubset monotone_def)
  apply (metis assms orsubset monotone_def)
  done

lemma boxdiamondmono : 
  assumes "mono f"
  shows "mono (\<lambda>S'. {s. \<forall> s'. (s, a, s') \<in> (transition M) \<longrightarrow>  s' \<in> f S'})"
  and "mono (\<lambda>S'. {s. \<exists> s'. (s, a, s') \<in> (transition M) \<and>  s' \<in> f S'})"
  apply (simp_all add: monotone_def)
  using assms monoD apply blast+
  done

lemma boxdiamondantimono : 
  assumes "antimono f"
  shows "antimono (\<lambda>S'. {s. \<forall> s'. (s, a, s') \<in> (transition M) \<longrightarrow>  s' \<in> f S'})"
  and "antimono (\<lambda>S'. {s. \<exists> s'. (s, a, s') \<in> (transition M) \<and>  s' \<in> f S'})"
  apply (simp_all add: monotone_def)
  using assms antimonoD apply blast+
  done

lemma numumono : 
  assumes "\<And>S''. mono (f S'')"
  shows "mono (\<lambda>S'. (\<Union> {S''. S'' \<subseteq> f S'' S'}))"
  and "mono (\<lambda>S'. (\<Inter> {S''. S'' \<supseteq> f S'' S'}))"
  apply (simp_all add: monotone_def)
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. S'' \<subseteq> f S'' x \<longrightarrow> S'' \<subseteq> f S'' y")
  apply blast
  using assms monotoneD apply fastforce
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. f S'' y \<subseteq> S'' \<longrightarrow> f S'' x \<subseteq> S''")
  apply blast
  using assms monotoneD apply fastforce
  done

lemma numuantimono : 
  assumes "\<And>S''. antimono (f S'')"
  shows "antimono (\<lambda>S'. (\<Union> {S''. S'' \<subseteq> f S'' S'}))"
  and "antimono (\<lambda>S'. (\<Inter> {S''. S'' \<supseteq> f S'' S'}))"
  apply (simp_all add: monotone_def)
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. S'' \<subseteq> f S'' y \<longrightarrow> S'' \<subseteq> f S'' x")
  apply blast
  using assms monotoneD apply fastforce
  apply (rule allI)+
  apply (rule impI)
  apply (subgoal_tac "\<forall>S''. f S'' x \<subseteq> S'' \<longrightarrow> f S'' y \<subseteq> S''")
  apply blast
  using assms monotoneD apply fastforce
  done

lemma monotonicitynotdepend :
"(notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (e(i := S')))))
 \<and> (notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (e(i := S')))))"
  apply (induct f arbitrary : i e; simp only: notdependalloccursposnegi.simps)
  apply (simp add: monotone_def)+
  apply (metis notdepends)
proof-
  fix f1 f2 i e
  assume assum1: "(\<And>i e. (notdependalloccursposnegi f1 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f1\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f1 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f1\<rbrakk> M e(i := S'))))"
  assume assum2: "(\<And>i e. (notdependalloccursposnegi f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f2\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f2\<rbrakk> M e(i := S'))))"
  have "\<not> dependvari (and' f1 f2) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormono)
  moreover have "notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andorantimono)
  ultimately show "(\<not> dependvari (and' f1 f2) M i \<or> notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (and' f1 f2) M i \<or> notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>and' f1 f2\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvari (or f1 f2) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andormono)
  moreover have "notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))" by (auto simp: assum1 assum2 andorantimono)
  ultimately show "(\<not> dependvari (or f1 f2) M i \<or> notdependalloccursposnegi f1 M i True \<and> notdependalloccursposnegi f2 M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (or f1 f2) M i \<or> notdependalloccursposnegi f1 M i False \<and> notdependalloccursposnegi f2 M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>or f1 f2\<rbrakk> M e(i := S')))" by auto
next
  fix a f i e
  assume assum1: "(\<And>i e. (notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))))"
  have "\<not> dependvari (box a f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmono)
  moreover have "notdependalloccursposnegi f M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondantimono)
  ultimately show "(\<not> dependvari (box a f) M i \<or> notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (box a f) M i \<or> notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>box a f\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvari (diamond a f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M i True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondmono)
  moreover have "notdependalloccursposnegi f M i False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))" by (auto simp: assum1 boxdiamondantimono)
  ultimately show "(\<not> dependvari (diamond a f) M i \<or> notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (diamond a f) M i \<or> notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>diamond a f\<rbrakk> M e(i := S')))" by auto
next
  fix f i e
  assume assum1: "(\<And>i e. (notdependalloccursposnegi f M i True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))) \<and> (notdependalloccursposnegi f M i False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>f\<rbrakk> M e(i := S'))))"
  have "\<not> dependvari (nu f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M (Suc i) True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numumono)
  moreover have "notdependalloccursposnegi f M (Suc i) False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numuantimono)
  ultimately show "(\<not> dependvari (nu f) M i \<or> notdependalloccursposnegi f M (Suc i) True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (nu f) M i \<or> notdependalloccursposnegi f M (Suc i) False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>nu f\<rbrakk> M e(i := S')))" by auto
  have "\<not> dependvari (mu f) M i \<longrightarrow> (mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')) \<and> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')))" using notdependsmono by metis
  moreover have "notdependalloccursposnegi f M (Suc i) True \<Longrightarrow> mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numumono)
  moreover have "notdependalloccursposnegi f M (Suc i) False \<Longrightarrow> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))" by (auto simp: assum1 numuantimono)
  ultimately show "(\<not> dependvari (mu f) M i \<or> notdependalloccursposnegi f M (Suc i) True \<longrightarrow> mono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S'))) \<and> (\<not> dependvari (mu f) M i \<or> notdependalloccursposnegi f M (Suc i) False \<longrightarrow> antimono (\<lambda>S'. \<lbrakk>mu f\<rbrakk> M e(i := S')))" by auto
qed

lemma monotonicitynotdependcoro : 
  shows "notdependalloccursposnegi f M 0 True \<Longrightarrow> mono (transformer f M e)"
  and "notdependalloccursposnegi f M 0 False \<Longrightarrow> antimono (transformer f M e)"
  apply (simp_all add: transformerdef)
proof-
  have "\<forall>S''. notdependalloccursposnegi f M 0 True \<longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicitynotdepend by metis
  thus "notdependalloccursposnegi f M 0 True \<Longrightarrow> mono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
next
  have "\<forall>S''. notdependalloccursposnegi f M 0 False \<longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M ((newenvironment e S'')(0 := S'))))" using monotonicitynotdepend by metis
  thus "notdependalloccursposnegi f M 0 False \<Longrightarrow> antimono (\<lambda>S'.(\<lbrakk>f\<rbrakk> M (newenvironment e S')))" by auto
qed

section \<open>Approximation of \<open>nu\<close> and \<open>mu\<close>.\<close>

lemma gfp_eq_nu [simp] :
"gfp (transformer f M e) = \<lbrakk>nu f\<rbrakk> M e"
  by (simp add: gfp_def transformer_def)

lemma lfp_eq_mu [simp] :
"lfp (transformer f M e) = \<lbrakk>mu f\<rbrakk> M e"
  by (simp add: lfp_def transformer_def)

lemma monosubset :
  assumes "mono f"
  shows "(f S' \<subseteq> S' \<longrightarrow> (f^^(Suc i)) S' \<subseteq> (f^^i) S') \<and>
    (S' \<subseteq> f S' \<longrightarrow> (f^^ i) S' \<subseteq> (f^^(Suc i)) S')"
  apply (induct i)
  using assms apply (simp_all add: mono_def)
  done

lemma fpoweriplusn : 
  assumes "((f :: 'a \<Rightarrow> 'a)^^i) S' = (f^^(Suc i)) S'"
  shows "(f^^(i + n)) S' = (f^^(Suc i + n)) S'" 
  apply (induct n)
  using assms apply simp
proof-
  fix n
  assume "(f ^^ (i + n)) S' = (f ^^ (Suc i + n)) S'"
  hence "f ((f ^^ (i + n)) S') = f ((f ^^ Suc (i + n)) S')" by simp
  thus "(f ^^ (i + Suc n)) S' = (f ^^ (Suc i + Suc n)) S'" by simp
qed

lemma fixpointmono:
  assumes "mono (f :: ('s set \<Rightarrow> 's set))"
  and "finite (UNIV :: 's set)"
  and "S' \<subseteq> f S' \<or> f S' \<subseteq> S'"
  shows "\<exists>n \<le> card(UNIV :: 's set). (f^^n) S' = (f^^(Suc n)) S'"
proof (rule ccontr)
  assume "\<not> (\<exists>n\<le>card(UNIV :: 's set).((f ^^ n) S') = ((f ^^ Suc n) S'))"
  hence assum1 : "\<forall>n\<le>card(UNIV :: 's set).((f ^^ n) S') \<noteq> ((f ^^ Suc n) S')" by auto
  {
    assume assum2 : "S' \<subseteq> f S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((f ^^ n) S') \<ge> n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> n \<le> card ((f ^^ n) S')"
        apply (induct n)
        apply simp
      proof
        fix n
        assume assum3: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> n \<le> card ((f ^^ n) S')"
        assume assum4 : "Suc n \<le> Suc (card (UNIV :: 's set))"
        hence "n \<le> (card (UNIV :: 's set))" by simp
        hence "(f ^^ n) S' \<noteq> (f ^^ (Suc n)) S'" using assum1 by simp
        moreover have "(f ^^ n) S' \<subseteq> (f ^^ (Suc n)) S'" using assms(1) assum2 monosubset by blast 
        ultimately have "(f ^^ n) S' \<subset> (f ^^ (Suc n)) S'" using psubset_eq by simp
        moreover have "finite ((f ^^ Suc n) S')" using assms(2) rev_finite_subset by auto
        ultimately have "card ((f ^^ n) S') < card ((f ^^ Suc n) S')" using psubset_card_mono by metis
        thus "Suc n \<le> card ((f ^^ Suc n) S')" using assum3 assum4 by simp
      qed
    qed
    hence contradiction1 : "card ((f ^^ Suc (card(UNIV :: 's set))) S') \<ge>  Suc (card(UNIV :: 's set))" by auto
    have contradiction2: "card ((f ^^ Suc (card(UNIV :: 's set))) S') \<le> card(UNIV :: 's set)" using assms(2) card_mono by auto
    have False using contradiction1 contradiction2 by auto
  }
  moreover{
    assume assum2 : "f S' \<subseteq> S'"
    have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((f ^^ n) S') < Suc(card(UNIV :: 's set)) - n"
    proof
      fix n
      show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> card ((f ^^ n) S') < Suc (card(UNIV :: 's set)) - n"
        apply (induct n)
        apply (simp add : assms(2) card_mono less_Suc_eq_le)
      proof
        fix n
        assume assum3: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> card ((f ^^ n) S') < Suc(card (UNIV :: 's set)) - n"
        assume assum4 : "Suc n \<le> Suc (card (UNIV :: 's set))"
        hence "n \<le> (card (UNIV :: 's set))" by simp
        hence "(f ^^ n) S' \<noteq> (f ^^ (Suc n)) S'" using assum1 by simp
        moreover have "(f ^^ (Suc n)) S' \<subseteq> (f ^^ n) S'" using assms(1) assum2 monosubset by blast 
        ultimately have "(f ^^ (Suc n)) S' \<subset> (f ^^  n) S'" using psubset_eq by simp
        moreover have "finite ((f ^^ n) S')" using assms(2) rev_finite_subset by auto
        ultimately have "card ((f ^^ (Suc n)) S') < card ((f ^^ n) S')" using psubset_card_mono by metis
        thus "card ((f ^^ Suc n) S') < Suc(card (UNIV :: 's set)) - (Suc n)" using assum3 assum4 by simp
      qed
    qed
    hence "card ((f ^^ Suc (card(UNIV :: 's set))) UNIV) <  0" by auto
    hence False by auto
  }
  ultimately show False using assms(3) by auto
qed

lemma gfp_monofin [simp] :
  assumes "finite (UNIV :: 's set)"
  and "mono (f :: 's set \<Rightarrow> 's set)"
  shows "(f^^(card (UNIV :: 's set))) UNIV = gfp f"
proof-
  have "\<exists>n \<le> card(UNIV :: 's set). (f^^n) (UNIV) = (f^^(Suc n)) (UNIV)" using assms fixpointmono by blast
  from this obtain n where assum2: "n \<le> card (UNIV :: 's set) \<and>  (f^^n) (UNIV) = (f^^(Suc n)) (UNIV)" by auto
  hence "(f ^^ (n + (card (UNIV :: 's set) - n))) (UNIV) = (f ^^ (Suc n +  (card (UNIV :: 's set) - n))) (UNIV)" using fpoweriplusn by metis
  hence "(f^^(card (UNIV :: 's set)))(UNIV) = (f^^Suc(card (UNIV :: 's set)))(UNIV)" using assum2 by auto
  thus ?thesis using gfp_Kleene_iter assms(2) by blast
qed

lemma lfp_monofin [simp] :
  assumes "finite (UNIV :: 's set)"
  and "mono (f :: 's set \<Rightarrow> 's set)"
  shows "(f^^(card (UNIV :: 's set))) {} = lfp f"
proof-
  have "\<exists>n \<le> card(UNIV :: 's set). (f^^n) {} = (f^^(Suc n)) {}" using assms fixpointmono by blast
  from this obtain n where assum2: "n \<le> card (UNIV :: 's set) \<and>  (f^^n) {} = (f^^(Suc n)) {}" by auto
  hence "(f ^^ (n + (card (UNIV :: 's set) - n))) {} = (f ^^ (Suc n +  (card (UNIV :: 's set) - n))) {}" using fpoweriplusn by metis
  hence "(f^^(card (UNIV :: 's set))){} = (f^^Suc(card (UNIV :: 's set))){}" using assum2 by auto
  thus ?thesis using lfp_Kleene_iter assms(2) by blast
qed

lemma transformer_eq_nu :
  assumes "finite (UNIV :: 's set)"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "\<lbrakk>nu f\<rbrakk> M e = ((transformer f M e)^^(card (UNIV :: 's set)))(UNIV)"
  using assms by auto 

lemma transformer_eq_mu :
  assumes "finite (UNIV :: 's set)"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "\<lbrakk>mu f\<rbrakk> M e = ((transformer f M e)^^(card (UNIV :: 's set))){}"
  using assms by auto

end
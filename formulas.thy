theory formulas
imports paths Main
begin

section \<open>negate formulas\<close>

lemma negtrue : "\<lbrakk>(neg tt)\<rbrakk> M e = \<lbrakk>ff\<rbrakk> M e"
  by (simp)

lemma negfalse : "\<lbrakk>(neg ff)\<rbrakk> M e = \<lbrakk>tt\<rbrakk> M e"
  by (simp)

lemma negnegf : "\<lbrakk>(neg (neg (f)))\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  by (simp)

lemma negand' : "\<lbrakk>(neg (and' f f'))\<rbrakk> M e = \<lbrakk>(or (neg f) (neg f'))\<rbrakk> M e"
  by (simp)

lemma negor : "\<lbrakk>(neg (or f f'))\<rbrakk> M e = \<lbrakk>(and' (neg f) (neg f'))\<rbrakk> M e"
  by (simp)

lemma negdiamond : "\<lbrakk>(neg (diamond act f))\<rbrakk> M e = \<lbrakk>(box act (neg f))\<rbrakk> M e"
  by (simp; auto)

lemma negbox : "formulasemantics (neg (box act f)) M e = formulasemantics (diamond act (neg f)) M e"
  by (simp; auto)

lemma complementuniontoexists [simp] : "s \<in> -(\<Union> {S. P S}) = (\<not>(\<exists> S. P S \<and> s \<in> S))"
  by auto

lemma intersectiontoforall [simp] : "s \<in> (\<Inter> {S. P S}) = (\<forall> S. P S \<longrightarrow> s \<in> S)"
  by auto

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
  apply (simp)
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
  from this show "(-\<Union> {S. S \<subseteq> formulasemantics f M (newenvironment e S)}) = (\<Inter> {S. - formulasemantics f M (newenvironment e (- S)) \<subseteq> S})" by blast
qed

(*and this one*)
lemma negnu : "formulasemantics (neg (nu f)) M e = formulasemantics (mu (neg (negvari f 0))) M e"
proof-
  have h : "formulasemantics (neg (nu f)) M e = (\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))})" using negnuinbetween by simp
  have "\<forall> e i. (formulasemantics (neg f) M (e(i := -e(i)))) = formulasemantics (negvari (neg f) i) M e"  
    apply (induct f)
  proof-
      show "\<forall> e i. (formulasemantics (neg tt) M (e(i := -e(i)))) =  (formulasemantics (negvari (neg tt) i) M e)" by simp
    next
      show "\<forall> e i. formulasemantics (neg ff) M (e(i := -e(i))) = formulasemantics (negvari (neg ff) i) M e" by simp
    next
      show "\<And>X. \<forall> e i. formulasemantics (neg (var X)) M (e(i := -e(i))) =  formulasemantics (negvari (neg (var X)) i) M e"
        by simp
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
  hence "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (negvari (neg f) 0) M (newenvironment e S)" by (simp only: newenvironmentzerocomplement)  
  hence  "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (neg (negvari f 0)) M (newenvironment e S)" by auto
  hence "(\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))}) = (\<Inter> {S. S \<supseteq> (formulasemantics (neg (negvari f 0)) M (newenvironment e (S)))})" by auto
  thus ?thesis using h by auto
qed

lemma negvarnegvar [simp] : "\<lbrakk>(negvari (negvari f i) i)\<rbrakk> M e = \<lbrakk>f\<rbrakk> M e"
  by (induct f arbitrary : i e; simp)

lemma negmu : "\<lbrakk>(neg (mu f))\<rbrakk> M e = \<lbrakk>(nu (neg (negvari f 0)))\<rbrakk> M e"
proof-
  have "formulasemantics (mu (neg (negvari (neg (negvari f 0)) 0))) M e = formulasemantics (neg (nu (neg (negvari f 0)))) M e" by (simp only: negnu)
  hence "formulasemantics (neg (mu (neg (negvari (neg (negvari f 0)) 0)))) M e = formulasemantics (neg (neg (nu (neg (negvari f 0))))) M e" by auto
  also have "... = formulasemantics (nu (neg (negvari f 0))) M e" by (simp add : negnegf)
  ultimately show ?thesis by auto
qed

lemma gfp_eq_nu [simp] :
"gfp (transformer f M e) = \<lbrakk>(nu f)\<rbrakk> M e"
by (simp add: gfp_def transformer_def)

lemma lfp_eq_mu [simp] :
"lfp (transformer f M e) = \<lbrakk>(mu f)\<rbrakk> M e"
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
  shows "formulasemantics (nu f) M e = ((transformer f M e)^^(card (UNIV :: 's set)))(UNIV)"
  using gfp_eq_nu gfp_transformer assms by auto  

lemma transformer_eq_mu [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "formulasemantics (mu f) M e = ((transformer f M e)^^(card (UNIV :: 's set))){}"
  using lfp_eq_mu lfp_transformer assms by auto

lemma largerandsmaller : "X - Suc 0 < i \<Longrightarrow> \<not> X \<le> i \<Longrightarrow> (P :: nat \<Rightarrow> bool) X"
  by auto

lemma largerandsmallerenv : "X - Suc 0 < i \<longrightarrow> \<not> X \<le> i \<longrightarrow> (e 0) = (e X)"
  using largerandsmaller by auto

lemma shiftdownnewenv_eq_newenvshiftdown [simp] : "shiftdownenv (newenvironment e S') (Suc i) = newenvironment (shiftdownenv e i) S'"
  apply (rule)
  apply (induct_tac x)
  apply (simp_all add: shiftdownenv_def newenvironment.cases)
  done

lemma shiftdownnewenvzero_eq_newenv [simp] : "shiftdownenv (newenvironment e S') 0 = e"
  apply (rule)
  apply (induct_tac x; simp add: shiftdownenv_def)
  done

lemma switchnewenvironmentshiftdown : "formulasemantics (shiftdown f (Suc i)) M (newenvironment (shiftdownenv e i) S') = 
  formulasemantics (shiftdown f (Suc i)) M (shiftdownenv (newenvironment e S') (Suc i))"
  by simp

lemma shiftdownlemma [simp] : "\<not>(occursvari f i) \<longrightarrow> (formulasemantics (shiftdown f i) M (shiftdownenv e i)) = (formulasemantics f M e)"
  apply (induct f arbitrary: e i; simp add: shiftdownenv_def)
  apply (rule largerandsmallerenv)
  apply (rule impI)
  apply (subst switchnewenvironmentshiftdown)
  prefer 2 
  apply (rule impI) 
  apply (subst switchnewenvironmentshiftdown)
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

lemma shiftdowncoro : "\<not>(occursvari f 0) \<longrightarrow> (formulasemantics (shiftdown f 0) M e) = (formulasemantics f M (newenvironment e S'))" 
  using shiftdownlemma shiftdownnewenvzero_eq_newenv by metis

lemma targetpath [simp]: 
"validfinpath M s p s' \<longrightarrow> s' \<in> insert s (set (map target p))"
  by (induct p arbitrary : s; simp)

lemma prop40rtl :
  assumes "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)
     \<and> insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)"
  and "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "finite A"
  shows "(s \<in> formulasemantics (mu (and' g (or f (Diamond (acts A) (var 0))))) (M :: ('a, 's) lts) e)"
  apply (simp add : newenvironment.cases assms(4) del: Diamond.simps)
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
    apply (induct p arbitrary : s; simp)
    apply (rule impI)
  proof-
    fix t p s
    assume assum3 : "(\<And>s. validfinpath M s p s' \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S' \<longrightarrow> s \<in> S')"
    assume assum4 : "s = source t \<and> t \<in> transition M \<and> validfinpath M (target t) p s' \<and> action t \<in> A \<and> action ` set p \<subseteq> A \<and> s \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target t \<in> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> target ` set p \<subseteq> \<lbrakk>shiftdown g 0\<rbrakk> M e \<and> s' \<in> S'"
    hence "target t \<in> S'" using assum3 by auto
    hence "(source t, action t, target t) \<in> transition M \<and> target t \<in> S'" using assum4 split by metis
    hence c1 : "source t \<in> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'}" using assum4 by blast
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
  shows "s \<in> ((transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)^^n){} \<longrightarrow>
  (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set p \<subseteq> A)
     \<and> s \<in> (formulasemantics (shiftdown g 0) M e)
     \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  apply (induct n arbitrary : s)
  apply (simp)
proof
  fix n s
  let ?f = "and' g (or f (Diamond (acts A) (var 0)))"
  let ?S' = "(transformer ?f M e ^^ n) {}"
  assume assum1 : "\<And>s. s \<in> ?S'
    \<longrightarrow> (\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))"
  let ?S'' = "(transformer ?f M e ^^ Suc n) {}"
  assume assum2 : "s \<in> ?S''"
  hence splitand : "(s \<in> formulasemantics g M (newenvironment e ?S')) 
    \<and> (s \<in> formulasemantics f M (newenvironment e ?S') \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'))" by (simp add: transformer_def assms(3) del: Diamond.simps)
  hence ing : "s \<in> (formulasemantics (shiftdown g 0) M e)" using shiftdowncoro assms by metis
  from splitand have "s \<in> formulasemantics f M (newenvironment e ?S') \<or> (\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S')" by auto
  moreover {
    assume assum3 : "s \<in> formulasemantics f M (newenvironment e ?S')"
    from assum3 have "s \<in> (formulasemantics (shiftdown f 0) M e)" by (metis assms(1) shiftdowncoro)
    hence "validfinpath M s [] s \<and> s \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set [] \<subseteq> A) \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set []) \<subseteq> (formulasemantics (shiftdown g 0) M e)" using ing by simp
    hence "\<exists>p s'. validfinpath M s p s' \<and> s' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A \<and> s \<in> (formulasemantics (shiftdown g 0) M e) \<and> (target ` set p) \<subseteq> (formulasemantics (shiftdown g 0) M e)" by blast
  }
  moreover {
    assume "\<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'"
    from this obtain s' act where assum3 : "act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> ?S'" by auto
    hence "\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" using assum1 by auto
    from this obtain p s'' where tail : "validfinpath M s' p s'' \<and> s'' \<in> formulasemantics (shiftdown f 0) M e \<and> action ` set p \<subseteq> A
      \<and> (s' \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set p \<subseteq> (formulasemantics (shiftdown g 0) M e))" by auto
    let ?p = "(s, act, s') # p"
    have "source (s, act, s') = s \<and> (s, act, s') \<in> transition M \<and> validfinpath M (target (s, act, s')) p s''" using assum3 tail by (simp)
    hence "validfinpath M s ?p s''" by auto
    hence "validfinpath M s ?p s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (action ` set ?p \<subseteq> A) \<and> 
      s \<in> (formulasemantics (shiftdown g 0) M e) \<and> target ` set ?p \<subseteq> (formulasemantics (shiftdown g 0) M e)" using assum3 ing tail by (simp)
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
  shows "mono (transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)"
  apply (simp add: assms(3))
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
  assumes "s \<in> formulasemantics (mu (and' g (or (f) (Diamond (acts A) (var 0))))) (M :: ('a, 's) lts) e"
  and "\<not>(occursvari f 0)"
  and "\<not>(occursvari g 0)"
  and "finite (UNIV :: 's set)"
  and "finite A"
  shows "(\<exists>p s'. validfinpath M s p s' 
        \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) 
        \<and> (set (map action p) \<subseteq>  A) 
        \<and> (insert s (set (map target p)) \<subseteq> (formulasemantics (shiftdown g 0) M e)))"
  apply (simp)
proof-
  have "mono (transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)" using assms(2) assms(3) assms(5) monotonicityformula40 by metis
  hence "s \<in> ((transformer (and' g (or f (Diamond (acts A) (var 0)))) M e)^^(card (UNIV :: 's set))){}" using assms(1) assms(4) transformer_eq_mu by auto 
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
  shows "(s \<in> formulasemantics (mu (and' g (or f (Diamond (acts A) (var 0))))) (M :: ('a, 's) lts) e) = 
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
    using assum1 by simp
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
    hence "validfinpath M s ((s, act , s')#p) s'' \<and> s'' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action ((s, act, s')#p)) \<subseteq> A)" using assum1 by simp
    thus False using assms(3) by blast
  qed
  thus ?thesis using assum1 by auto
qed

lemma theorem21generalizedltr : 
  assumes "\<not>(occursvari f 0)"
  and "(s \<in> formulasemantics (nu (or f (Diamond (acts A) (var 0)))) M e)"
  and "finite A"
  shows "((\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or>
    (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))"
proof-
  have "\<exists>S'. S' \<subseteq> \<lbrakk>f\<rbrakk> M (newenvironment e S') \<union> {s. \<exists>s' act. act \<in> A \<and> (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'" using assms(2) assms(3) by (simp del : Diamond.simps)
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
  shows "(s \<in> formulasemantics (nu (or f (Diamond (acts A) (var 0)))) M e)"
  apply (simp add: assms(2) del: Diamond.simps)
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
        thus "source t \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<or> (\<exists>s' act. act \<in> A \<and> (source t, act, s') \<in> transition M \<and> (\<exists>p s''. validfinpath M s' p s'' \<and> s'' \<in> \<lbrakk>shiftdown f 0\<rbrakk> M e \<and> action ` set p \<subseteq> A))" by blast
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
      hence "(s, action (p 0), target (p 0)) \<in> transition M  \<and> action (p 0) \<in> A \<and> validinfpath M (target (p 0)) (suffix (Suc 0) p) \<and> (\<forall>n. action ((suffix (Suc 0) p) n) \<in> A)" by simp
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
  shows "(s \<in> \<lbrakk>nu (or f (Diamond (acts A) (var 0)))\<rbrakk> M e) =
  ((\<exists>p s'. validfinpath M s p s' \<and> s' \<in> (formulasemantics (shiftdown f 0) M e) \<and> (set (map action p) \<subseteq> A)) \<or> 
  (\<exists>p. validinfpath M s p \<and> (\<forall>n. action (p n) \<in> A)))"
  apply (rule iffI)
  using assms theorem21generalizedltr apply metis
  using assms theorem21generalizedrtl apply metis
  done

lemma Boxcomplement_locked : "finite (-B) \<Longrightarrow> (s \<in> \<lbrakk>Box (acts (-B)) ff\<rbrakk> M e = locked M B s)"
  apply (simp add: locked_def enabledactions_def del: Box.simps)
  apply (blast)
  done

lemma finitesubsetUNIV [simp] : "finite (UNIV :: 'a set) \<Longrightarrow> finite (A :: 'a set)"
  using finite_subset subset_UNIV by blast

lemma validfinpathmatchacts [simp] : "(validfinpath M s p s' \<and> match (acts A) p) = (\<exists>a \<in> A. (s, a, s') \<in> transition M \<and> p = [(s, a, s')])"
  by (simp add: match_def; auto)

value "(concat [[1, 2], [3, 4]]) :: nat list"

lemma shiftupnotoccurs [simp] : "\<not>(occursvari (shiftup f i) i)"
  by (induct f arbitrary : i; simp)

lemma shiftuplemma [simp] : "\<lbrakk>shiftup f 0\<rbrakk> M (newenvironment e S') = \<lbrakk>f\<rbrakk> M e"
proof-
  have "(formulasemantics (shiftdown (shiftup f 0) 0) M (shiftdownenv (newenvironment e S') 0)) = (formulasemantics (shiftup f 0) M (newenvironment e S'))" using shiftupnotoccurs shiftdownlemma by metis
  thus "(formulasemantics (shiftup f 0) M (newenvironment e S')) = (formulasemantics f M e)" using shiftupanddown shiftdownnewenvzero_eq_newenv by metis
qed

lemma Diamondactsempty [simp] : "\<lbrakk>f\<rbrakk> M e = {} \<Longrightarrow> \<lbrakk>Diamond (acts A) f\<rbrakk> M e = {}"
proof-
  assume assum1: "\<lbrakk>f\<rbrakk> M e = {}"
  have "\<forall>listA. \<lbrakk>Diamondlist (listA) f\<rbrakk> M e = {}"
    apply (rule allI)
    apply (induct_tac listA; simp add: assum1)
    done
  thus "\<lbrakk>Diamond (acts A) f\<rbrakk> M e = {}" by auto
qed

lemma Diamondempty [simp] : "\<lbrakk>f\<rbrakk> M e = {} \<Longrightarrow> \<lbrakk>Diamond R f\<rbrakk> M e = {}"
  apply (induct R arbitrary : f e)
  prefer 2
  apply (rule Diamondactsempty)
  apply (simp_all)
  apply (auto)
  done

lemma inductionstepmatch :
  assumes "\<And>f s e. (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)"
  shows "(\<exists>p s'. validfinpath M s p s' \<and> match (repeat R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e) \<Longrightarrow> (s \<in> formulasemantics (Diamond (repeat R) f) M e)"
  apply (simp)
  apply (rule allI)
proof
  fix S'
  assume "\<exists>p s'. validfinpath M s p s' \<and> (\<exists>n. matchntimes n R p) \<and> s' \<in> \<lbrakk>f\<rbrakk> M e"
  from this obtain p s' n where assum1 : " s' \<in> \<lbrakk>f\<rbrakk> M e \<and> matchntimes n R p \<and> validfinpath M s p s'" by auto
  assume assum2 : "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S') \<subseteq> S' \<and> \<lbrakk>f\<rbrakk> M e \<subseteq> S'"
  have "(s' \<in> \<lbrakk>f\<rbrakk> M e \<and> matchntimes n R p \<and> validfinpath M s p s') \<Longrightarrow> s \<in> S'"
    apply (induct n arbitrary: s p; simp)
  proof-
    show "s' \<in> \<lbrakk>f\<rbrakk> M e \<Longrightarrow> s' \<in> S'" using assum1 assum2 emptypath by auto
    fix n s p
    assume assum3 : "(\<And>s p. matchntimes n R p \<and> validfinpath M s p s' \<Longrightarrow> s \<in> S')"
    assume "s' \<in> \<lbrakk>f\<rbrakk> M e \<and> (\<exists>p' p''. p = p' @ p'' \<and> match R p' \<and> matchntimes n R p'') \<and> validfinpath M s p s'"
    hence "\<exists>p' p''. s' \<in> \<lbrakk>f\<rbrakk> M e \<and>  match R p' \<and> matchntimes n R p'' \<and> validfinpath M s (p' @ p'') s'" by auto
    hence "\<exists>p' p'' s''. s' \<in> \<lbrakk>f\<rbrakk> M e \<and>  match R p' \<and> matchntimes n R p'' \<and> validfinpath M s p' s'' \<and> validfinpath M s'' p'' s'" using validfinpathsplit by auto
    from this obtain p' p'' s'' where assum4 : "s' \<in> \<lbrakk>f\<rbrakk> M e \<and>  match R p' \<and> matchntimes n R p'' \<and> validfinpath M s p' s'' \<and> validfinpath M s'' p'' s'" by blast
    hence "s'' \<in> S'" using assum3 by auto
    hence "s'' \<in> \<lbrakk>var 0\<rbrakk> M (newenvironment e S')" by simp
    hence "(validfinpath M s p' s'' \<and> match R p' \<and> s'' \<in> \<lbrakk>var 0\<rbrakk> M (newenvironment e S'))" using assum4 by auto
    hence "s \<in> \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e S')" using assms by auto
    thus "s \<in> S'" using assum2 by auto
  qed
  thus "s \<in> S'" using assum1 by auto
qed

lemma Diamondmatch :
  assumes "finite (UNIV :: 'a set)"
  shows "s \<in> \<lbrakk>Diamond (R :: 'a regularformula) f\<rbrakk> M e = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)"
  apply (induct R arbitrary : f s e)
  apply (simp)
  apply (subst Diamond_eq_exist)
  using assms(1) apply (rule finitesubsetUNIV)
  apply (simp; force)
  prefer 2
  apply auto[1]
   prefer 2
proof
  fix R f s e
  show "(\<And>f s e. (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e)) \<Longrightarrow> \<exists>p s'. validfinpath M s p s' \<and> match (repeat R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e \<Longrightarrow> s \<in> \<lbrakk>Diamond (repeat R) f\<rbrakk> M e" by (rule inductionstepmatch)
next
  fix R f s e
  assume assum1 : "(\<And>f s e. (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e))"
  assume assum2 : "s \<in> \<lbrakk>Diamond (repeat R) f\<rbrakk> M e"
  let ?S' = "{s. \<exists>p s' n. validfinpath M s p s' \<and> matchntimes n R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e}"
  have "\<lbrakk>f\<rbrakk> M e \<subseteq> ?S'"
  proof
    fix s
    assume "s \<in> \<lbrakk>f\<rbrakk> M e"
    hence "validfinpath M s [] s \<and> matchntimes 0 R [] \<and> s \<in> \<lbrakk>f\<rbrakk> M e" by auto
    then show "s \<in> ?S'" by blast
  qed
  moreover have "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S') \<subseteq> ?S'"
  proof
    fix s 
    assume "s \<in> \<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S')"
    hence "\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> ?S'" using assum1 by auto
    from this obtain p s' p' s'' n where assum3 : "validfinpath M s p s' \<and> match R p \<and> validfinpath M s' p' s'' \<and> matchntimes n R p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e" by blast
    hence "validfinpath M s (p @ p') s''" using validfinpathsplit by metis
    moreover have "matchntimes (Suc n) R (p @ p') \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e" using assum3 by auto
    ultimately show "s \<in> ?S'" by blast
  qed
  ultimately have "\<lbrakk>Diamond R (var 0)\<rbrakk> M (newenvironment e ?S') \<union> \<lbrakk>f\<rbrakk> M e \<subseteq> ?S'" by auto
  thus "\<exists>p s'. validfinpath M s p s' \<and> match (repeat R) p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e" using assum2 by auto
next
  fix R Q f s e
  assume "(\<And>f s e. (s \<in> \<lbrakk>Diamond R f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e))"
  hence assum1 : "(s \<in> \<lbrakk>Diamond R (Diamond Q f)\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match R p \<and> s' \<in> \<lbrakk>Diamond Q f\<rbrakk> M e)" by auto
  assume "(\<And>f s e. (s \<in> \<lbrakk>Diamond Q f\<rbrakk> M e) = (\<exists>p s'. validfinpath M s p s' \<and> match Q p \<and> s' \<in> \<lbrakk>f\<rbrakk> M e))"
  hence "(s \<in> \<lbrakk>Diamond R (Diamond Q f)\<rbrakk> M e) = (\<exists>p p' s''. (\<exists>s'. validfinpath M s p s' \<and> validfinpath M s' p' s'') \<and> match R p \<and> match Q p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)" using assum1 by blast
  hence "(s \<in> \<lbrakk>Diamond R (Diamond Q f)\<rbrakk> M e) = (\<exists>p p' s''. validfinpath M s (p @ p') s'' \<and> match R p \<and> match Q p' \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)" by simp
  thus "(s \<in> \<lbrakk>Diamond (after R Q) f\<rbrakk> M e) = (\<exists>p s''. validfinpath M s p s'' \<and> match (after R Q) p \<and> s'' \<in> \<lbrakk>f\<rbrakk> M e)" by auto
qed

lemma theorem21 :
  assumes "finite (UNIV :: 'a set)" (*introduce definition for finite regular formulas*)
  shows "s \<in> \<lbrakk>neg (Diamond \<rho> (nu (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (-B)) ff)) (Diamond (acts (-\<alpha>\<^sub>f)) (var 0)))))\<rbrakk> (M :: ('a, 's)lts) e 
    = (\<nexists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p)"
proof-
  have "\<forall>s. s \<in> \<lbrakk>Diamond \<rho> (nu (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (-B)) ff)) (Diamond (acts (-\<alpha>\<^sub>f)) (var 0))))\<rbrakk> (M :: ('a, 's)lts) e 
    = (\<exists>p. violating p \<rho> \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s B p )"
    apply (subst Diamondmatch)
    apply (simp add: assms)
    apply (subst splitviolating)
  proof
    have "\<forall>s'. (s' \<in> \<lbrakk>nu (or (or (Diamond (acts \<alpha>\<^sub>e) tt) (Box (acts (- B)) ff)) (Diamond (acts (- \<alpha>\<^sub>f)) (var 0)))\<rbrakk> M e = 
    (\<exists>p'. violating p' eps \<alpha>\<^sub>f \<alpha>\<^sub>e \<and> progressing M s' B p'))"
      apply (subst violatingempty)
      apply (subst theorem21generalized; simp add: assms del: Box.simps Diamond.simps)
(*this is not finished as paths is not finished*)
(*also it still needs some arbitrary lemmas like 
shiftdown (Diamond (acts A) f) 0 = (Diamond (acts A) (shiftdown f 0))*)
  

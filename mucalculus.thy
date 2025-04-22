theory mucalculus
imports Main
begin

datatype 'Act formula =
  tt | ff | var nat |
  neg "'Act formula" |
  and' "'Act formula" "'Act formula" | 
  or "'Act formula" "'Act formula" | 
  box 'Act "'Act formula" |
  diamond 'Act "'Act formula" |
  nu "'Act formula" |
  mu "'Act formula"

value "diamond 2 (box 1 tt) :: nat formula"
value "nu (var 0) :: nat formula "

record ('Act, 'State) lts =
transition :: "('State * 'Act * 'State) set"
initial :: "'State set"

fun newenvironment :: "(nat \<Rightarrow> 'State set) \<Rightarrow> 'State set \<Rightarrow> (nat \<Rightarrow> 'State set) " where
"newenvironment e S 0 = S" |
"newenvironment e S (Suc n) = e n"

fun formulasemantics :: "'Act formula \<Rightarrow> ('Act, 'State) lts \<Rightarrow> (nat \<Rightarrow> 'State set)  \<Rightarrow> 'State set "
where 
  "(formulasemantics tt M e) = UNIV " |
  "(formulasemantics ff M e) =  {}" |
  "(formulasemantics (var X) M e)  = e X" |
  "(formulasemantics (neg f) M e) = -(formulasemantics  f M e)" |
  "(formulasemantics (and' f f') M e) = (formulasemantics f M e) \<inter> (formulasemantics f' M e)" |
  "(formulasemantics (or f f') M e) = (formulasemantics f M e) \<union> (formulasemantics f' M e)" |
  "(formulasemantics (diamond act f) M e) = {s. \<exists> s'. (s, act, s') \<in> (transition M) \<and> s'\<in> (formulasemantics f M e)}" |
  "(formulasemantics (box act f) M e) = {s. \<forall> s'. (s, act, s') \<in> (transition M) \<longrightarrow>  s'\<in> (formulasemantics f M e) }" |
  "(formulasemantics (nu f) M e) = \<Union> {S'. S' \<subseteq> (formulasemantics f M (newenvironment e S'))}" |
  "(formulasemantics (mu f) M e) = \<Inter> {S'. S' \<supseteq> (formulasemantics f M (newenvironment e S'))}"

fun negvari :: "'Act formula \<Rightarrow> nat \<Rightarrow> 'Act formula "
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

lemma nuX_X : "formulasemantics (nu (var 0)) M e = UNIV"
  apply (simp add: formulasemantics.cases newenvironment.cases)
  done

type_synonym 'State path = "nat \<Rightarrow> 'State"

definition validactionpath :: "('Act, 'State) lts \<Rightarrow> 'Act \<Rightarrow> 'State path \<Rightarrow> bool" where 
"validactionpath M act p = (\<forall> n.((p n), act, (p (Suc n))) \<in> transition M)"

lemma nuX_diamondactionrtl [simp] :
  assumes "\<exists> p. validactionpath M act p \<and> p 0 = s"
  shows "s \<in> formulasemantics (nu (diamond act (var 0))) M e "
  apply (simp)
proof-
  from assms obtain p where assum : "validactionpath M act p \<and> p 0 = s" by (rule exE)
  show "\<exists>S'. S' \<subseteq> {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> S'} \<and> s \<in> S'"
  proof (rule exI)
  let ?S' = "{s'. (\<exists>n. p n = s')}"
  have con1 : "s \<in> ?S'" using assum by auto
  have "?S' \<subseteq> {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> ?S'}"
    proof
      fix s
      assume "s \<in> {s'.\<exists>n. p n = s'}"
      from this obtain n where rewr : "s = p n"  by auto
      have nexttrans: "(s, act, p (Suc n)) \<in> (transition M)" using assum rewr by (simp add: validactionpath_def)
      have "p (Suc n) \<in> {s'.\<exists>n. p n = s'}" by auto
      hence "\<exists> s'.((s, act, s') \<in> (transition M) \<and> s' \<in> {s'.\<exists>n. p n = s'})" using nexttrans by auto
      thus "s \<in> {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> {s'.\<exists>n. p n = s'}}" by auto
    qed
  thus "?S' \<subseteq> {s. \<exists>s'. (s, act, s') \<in> transition M \<and> s' \<in> ?S'} \<and> s \<in> ?S'" using con1 by auto
  qed
qed

fun recursivepath :: "('State \<Rightarrow> 'State) \<Rightarrow> 'State \<Rightarrow> nat \<Rightarrow> 'State" where
"recursivepath succ s 0 = s" | 
"recursivepath succ s (Suc n) = succ (recursivepath succ s n)"

lemma succesorlemma [simp]: 
  assumes "\<exists> S'. (s \<in> S' \<and> (\<exists> succ :: ('State \<Rightarrow> 'State).\<forall>s'. s' \<in> S' \<longrightarrow> ((s', act, (succ s')) \<in> (transition M) \<and> (succ s') \<in> S')))"
  shows "(\<exists> p. validactionpath M act p \<and> p 0 = s)"
proof -
  from assms obtain S' where a: "(s \<in> S' \<and> (\<exists> succ :: ('State \<Rightarrow> 'State). \<forall> s'. s' \<in> S' \<longrightarrow> ((s', act, (succ s')) \<in> (transition M) \<and> (succ s') \<in> S')))" by blast
  hence "\<exists> succ :: ('State \<Rightarrow> 'State).\<forall> s'. s' \<in> S' \<longrightarrow> ((s', act, (succ s')) \<in> (transition M) \<and> (succ s') \<in> S')" by auto
  from this obtain succ where b: "\<forall>s'. s' \<in> S' \<longrightarrow> ((s', act, (succ s')) \<in> (transition M) \<and> (succ s') \<in> S')" by auto
  let ?p = "recursivepath succ s"
  have c1 : "?p 0 = s" by (simp add: recursivepath.cases)
  have "\<forall> n.((?p n, act , ?p (Suc n)) \<in> transition M \<and> ?p n \<in> S') " 
  proof
  fix m
  have "((?p m, act , ?p (Suc m)) \<in> transition M \<and> ?p m \<in> S')"
  proof
    (induct_tac m)
    have "s \<in> S'" using a by auto
    hence "(s, act, succ s) \<in> transition M  \<and> s \<in> S'" using b by auto
    hence "(recursivepath succ s 0, act, recursivepath succ s (Suc 0)) \<in> transition M \<and> recursivepath succ s 0 \<in> S'" by (simp add: recursivepath.cases)
    thus "(recursivepath succ s 0, act, recursivepath succ s (Suc 0)) \<in> transition M \<and> recursivepath succ s 0 \<in> S'" by auto
  next
    fix m
    assume assum: "(recursivepath succ s m, act, recursivepath succ s (Suc m)) \<in> transition M \<and> recursivepath succ s m \<in> S'"
    hence a2: "recursivepath succ s m \<in> S'" by auto
    hence "succ (recursivepath succ s m) \<in> S'" using b by auto
    hence e: "recursivepath succ s (Suc m) \<in> S'" by (simp add: recursivepath.cases)
    hence "(recursivepath succ s (Suc m), act, succ (recursivepath succ s (Suc m))) \<in> transition M" using b by auto
    hence "(recursivepath succ s (Suc m), act, recursivepath succ s (Suc (Suc m))) \<in> transition M" by (simp add: recursivepath.cases)
    hence "(recursivepath succ s (Suc m), act, recursivepath succ s (Suc (Suc m))) \<in> transition M \<and> recursivepath succ s (Suc m) \<in> S'" using e by auto
    thus  "(recursivepath succ s (Suc m), act, recursivepath succ s (Suc (Suc m))) \<in> transition M \<and> recursivepath succ s (Suc m) \<in> S'" by auto
  qed
  thus "((?p m, act, ?p (Suc m)) \<in> transition M \<and> ?p m \<in> S')" by auto
qed
  hence "validactionpath M act ?p" by (simp add: validactionpath_def)
  hence "validactionpath M act ?p \<and> ?p 0 = s" using c1 by auto
  thus ?thesis by blast
qed   

lemma nuX_diamondactionltr [simp] :
  assumes "s \<in> formulasemantics (nu (diamond act (var 0))) M e "
  shows "\<exists> p. validactionpath M act p \<and> p 0 = s"
proof -
  have "s \<in> formulasemantics (nu (diamond act (var 0))) M e" using assms by auto
  hence "s \<in> \<Union> {S'. S' \<subseteq> {s. \<exists> s'. (s, act, s') \<in> (transition M) \<and>  s'\<in> S'}}" by (simp add: formulasemantics.cases newenvironment.cases)
  hence "\<exists> S'. s \<in> S' \<and> S' \<subseteq> {s. \<exists> s'. (s, act, s') \<in> (transition M) \<and>  s'\<in> S'}" by auto
  from this obtain S' where b: "s \<in> S' \<and> S' \<subseteq> {s. \<exists> s'. (s, act, s') \<in> (transition M) \<and>  s'\<in> S'}" by auto
  hence  "\<exists> S'. (s \<in> S' \<and> (\<forall>s'. s' \<in> S' \<longrightarrow>(\<exists> s''. ((s', act, (s'')) \<in> (transition M) \<and> (s'') \<in> S'))))" by auto
  hence "\<exists> S'. (s \<in> S' \<and> (\<exists> succ.(\<forall>s'. s' \<in> S' \<longrightarrow> ((s', act, (succ s')) \<in> (transition M) \<and> (succ s') \<in> S'))))" by metis
  thus ?thesis by simp
qed

lemma nuX_diamondaction : "(s \<in> formulasemantics (nu (diamond act (var 0))) M e) =
(\<exists> p. validactionpath M act p \<and> p 0 = s)"
  apply (metis nuX_diamondactionrtl nuX_diamondactionltr)
  done

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

lemma newenvironmentlemma [simp] : "(newenvironment e S)((Suc i) := - ((newenvironment e S) (Suc i))) = newenvironment (e(i := - e i)) S"
proof
  fix n
  show "((newenvironment e S) (Suc i := - newenvironment e S (Suc i))) n = newenvironment (e(i := - e i)) S n"
    apply (induct n)
    apply (simp_all)
    done
qed

lemma newenvironmentzero [simp] : "(newenvironment e S)(0 := (-(newenvironment e S) 0)) = (newenvironment e (-S))"
proof
  fix n
  show "((newenvironment e S)(0 := ((-(newenvironment e S) 0)))) n  = (newenvironment e (-S)) n " by (metis fun_upd_def newenvironment.simps(1) newenvironment.simps(2) old.nat.exhaust)
qed

lemma switchcomplementnegationnu [simp] :
  assumes  "(\<And> e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e)"
  shows    "(\<And> e i. formulasemantics (neg (nu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (nu f)) i ) M e)"
proof-
  fix e
  fix i
have "\<And> S. (formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S))" using assms by blast
moreover have "\<And> S. (formulasemantics f M (newenvironment (e(i := - e i)) S)
   = formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))))" by (simp only : newenvironmentlemma)
hence "\<And> S. ((formulasemantics f M (newenvironment (e(i := - e i)) S) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S)))" using assms by blast
thus "formulasemantics (neg (nu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (nu f)) i) M e" by simp 
qed

lemma switchcomplementnegationmu [simp] :
  assumes  "(\<And> e i. formulasemantics f M (e(i := - e i)) = formulasemantics (negvari f i) M e)"
  shows    "(\<And> e i. formulasemantics (neg (mu f)) M (e(i := -e(i))) = formulasemantics (negvari (neg (mu f)) i) M e)"
proof-
  fix e
  fix i
have "\<And> S. (formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S))" using assms by blast
moreover have "\<And> S. (formulasemantics f M (newenvironment (e(i := - e i)) S)
   = formulasemantics f M ((newenvironment e S)((Suc i) := - ((newenvironment e S)) (Suc i))))" by (simp only : newenvironmentlemma)
hence "\<And> S. ((formulasemantics f M (newenvironment (e(i := - e i)) S) =
               formulasemantics (negvari f (Suc i)) M (newenvironment e S)))" using assms by blast
thus "formulasemantics (neg (mu f)) M (e(i := - e i)) = formulasemantics (negvari (neg (mu f)) i) M e" by simp 
qed

lemma negnuinbetween [simp]  : "(formulasemantics (neg (nu f)) M e) = (\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))})"
proof -
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

lemma negnu : "formulasemantics (neg (nu f)) M e = formulasemantics (mu (neg (negvari f 0))) M e"
proof-
  have h : "formulasemantics (neg (nu f)) M e = (\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))})" by (metis negnuinbetween)
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
  hence "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (negvari (neg f) 0) M (newenvironment e S)" by (simp only : newenvironmentzero)  
  hence  "\<And> S. formulasemantics (neg f) M ((newenvironment e (-S))) = formulasemantics (neg (negvari f 0)) M (newenvironment e S)" by auto
  hence "(\<Inter> {S. S \<supseteq> (formulasemantics (neg f) M (newenvironment e (-S)))}) = (\<Inter> {S. S \<supseteq> (formulasemantics (neg (negvari f 0)) M (newenvironment e (S)))})" by auto
  thus ?thesis using h by auto
qed

lemma negvarnegvar [simp] : "\<forall>i e. formulasemantics (negvari (negvari f i) i) M e = formulasemantics f M e"
  apply (induct f) 
  apply (simp_all add : formulasemantics.cases)
  done

lemma negmu : "formulasemantics (neg (mu f)) M e = formulasemantics (nu (neg (negvari f 0))) M e"
proof-
  have "\<forall> e. (formulasemantics f M e = formulasemantics (neg (negvari (neg (negvari f 0)) 0)) M e)" by simp
  have h1 : "formulasemantics (neg (mu f)) M e = formulasemantics (neg (mu (neg (negvari (neg (negvari f 0)) 0)))) M e" by simp
  have "formulasemantics (mu (neg (negvari (neg (negvari f 0)) 0))) M e = formulasemantics (neg (nu (neg (negvari f 0)))) M e" by (simp only: negnu)
  hence h2 : "formulasemantics (neg (mu (neg (negvari (neg (negvari f 0)) 0)))) M e = formulasemantics (neg (neg (nu (neg (negvari f 0))))) M e" by auto
  also have h3 : "formulasemantics (neg (neg (nu (neg (negvari f 0))))) M e = formulasemantics (nu (neg (negvari f 0))) M e" by (simp add : negnegf)
  thus ?thesis using h1 h2 h3 by auto
qed

fun approximationi :: "('s set \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> nat \<Rightarrow> 's set "
where 
  "approximationi T S 0  = S" | 
  "approximationi T S (Suc i)  = approximationi T (T S) i "

fun transformer :: "'a formula \<Rightarrow> ('a, 's) lts \<Rightarrow> (nat \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's set "
  where
"transformer f M e S' = formulasemantics f M (newenvironment e S')"

lemma lfp_eq_mu [simp] :
  assumes "mono (transformer f M e)"
  shows  "lfp (transformer f M e) = formulasemantics (mu f) M e"
proof-
  have unfold : "lfp (transformer f M e) = (transformer f M e)(lfp (transformer f M e)) " using assms lfp_unfold by blast
  have lowerbound : "\<forall>S'.(transformer f M e S') \<subseteq> S' \<longrightarrow> lfp (transformer f M e) \<subseteq> S'" using lfp_lowerbound by blast
  have "formulasemantics (mu f) M e =  \<Inter> {S'. S' \<supseteq> (transformer f M e S')}" by (simp add: formulasemantics.cases)
  thus ?thesis using unfold lowerbound by (simp add: lfp_def)
qed

lemma lfp_transformer [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "mono (transformer f (M :: ('a, 's) lts) e)"
  shows "((transformer f M e)^^(card (UNIV :: 's set))){} = lfp (transformer f M e)"
proof-
  have "((transformer f M e)^^(card (UNIV :: 's set))){} = ((transformer f M e)^^Suc(card (UNIV :: 's set))){}"
  proof-
    have a: "\<forall>i. ((transformer f M e)^^i) {} \<subseteq> ((transformer f M e)^^(Suc i)) {}" using assms(2) by (metis Suc_leD empty_subsetI funpow_mono2 nle_le)
    have "\<exists>n \<le> card(UNIV :: 's set).  ((transformer f M e)^^n) {} = ((transformer f M e)^^(Suc n)) {}"
    proof (rule ccontr)
      assume "\<not> (\<exists>n\<le>card(UNIV :: 's set).((transformer f M e ^^ n) {}) = ((transformer f M e ^^ Suc n) {}))"
      hence b: "\<forall>n\<le>card(UNIV :: 's set).((transformer f M e ^^ n) {}) \<noteq> ((transformer f M e ^^ Suc n) {})" by auto
      have  "\<forall>n \<le> Suc (card(UNIV :: 's set)). card ((transformer f M e ^^ n) {}) \<ge> n"
      proof
        fix n
        show "n \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> n \<le> card ((transformer f M e ^^ n) {})"
        proof (induct_tac n)
          show " 0 \<le> Suc (card(UNIV :: 's set)) \<longrightarrow> 0 \<le> card ((transformer f M e ^^ 0) {})" by auto
          fix n
          assume as1: "n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> n \<le> card ((transformer f M e ^^ n) {})"
          show "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> Suc n \<le> card ((transformer f M e ^^ Suc n) {})"
          proof-
            have as2: "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> n \<le> card(UNIV :: 's set)" by auto
            hence h1 : "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> (transformer f M e ^^ Suc n) {} \<noteq> (transformer f M e ^^ n) {}" using b by auto
            have h2 : "(transformer f M e ^^ Suc n) {} \<supseteq> (transformer f M e ^^ n) {}" using a by auto 
            have h3 : "finite ((transformer f M e ^^ Suc n) {})" using assms(1) rev_finite_subset by auto
            hence "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> (card ((transformer f M e ^^ Suc n) {}) > card ((transformer f M e ^^ n) {}))" using h1 h2 h3 by (metis psubset_card_mono psubset_eq)
            thus "Suc n \<le> Suc (card (UNIV :: 's set)) \<longrightarrow> Suc n \<le> card ((transformer f M e ^^ Suc n) {})" using as1 as2 by auto
          qed
        qed
      qed
      hence contradiction1 : "card ((transformer f M e ^^ Suc (card(UNIV :: 's set))) {}) \<ge>  Suc (card(UNIV :: 's set))" by auto
      have contradiction2: "card ((transformer f M e ^^ Suc (card(UNIV :: 's set))) {}) \<le> card(UNIV :: 's set)" using assms(1) card_mono by auto
      thus False using contradiction1 contradiction2 by auto
    qed
    thus ?thesis by (metis Kleene_iter_lpfp a assms(2) funpow_decreasing lfp_Kleene_iter lfp_fixpoint order_antisym_conv)
  qed
  thus ?thesis using lfp_Kleene_iter assms(2) by blast
qed

lemma existspathlengthi [simp] : 
"\<forall>i. \<forall>s. (s \<in> ((transformer (or (diamond act1 tt) (diamond act2 (var 0))) M e)^^(Suc i)){}
 \<longrightarrow>(\<exists>p. \<exists>n \<le> i. 
 p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m < n. (p m, act2, p (Suc m)) \<in> transition M)))"
  apply (rule allI)
proof-
  fix i
  show "\<forall>s. (s \<in> ((transformer (or (diamond act1 tt) (diamond act2 (var 0))) M e)^^(Suc i)){}
 \<longrightarrow>(\<exists>p n. n \<le> i \<and> 
 p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m < n. (p m, act2, p (Suc m)) \<in> transition M)))"
    apply (rule allI)
    apply (rule)
  proof (induct i)
    case 0
    fix s
    assume "s \<in> (transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e ^^ Suc 0) {}"
    hence "\<exists>s'. (s, act1, s') \<in> transition M" by (simp add: newenvironment.cases)
    from this obtain s' where a : "(s, act1, s') \<in> transition M" by (rule exE)
    show "\<exists>p. \<exists>n \<le> 0. p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (p m, act2, p (Suc m)) \<in> transition M)"
    proof
      let ?p = "\<lambda>n. (if n = 0 then s else s')"
      show "\<exists>n \<le> 0. ?p 0 = s \<and> (?p n, act1, ?p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (?p m, act2, ?p (Suc m)) \<in> transition M)" using a by auto
      qed
  next
    case (Suc i)
    fix i
    assume assum1 : "\<And>s. s \<in> (transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e ^^ Suc i) {} \<Longrightarrow> \<exists>p. \<exists>n \<le> i. p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (p m, act2, p (Suc m)) \<in> transition M)"
    fix s
    assume assum2 : "s \<in> (transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e ^^ Suc (Suc i)) {}"
    hence casesor : "(\<exists>s'. (s, act1, s') \<in> transition M) \<or> (\<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> (transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e ^^ (Suc i)) {})" by (simp add : newenvironment.cases)
    moreover {
      assume "\<exists>s'. (s, act1, s') \<in> transition M"
      from this obtain s' where a : "(s, act1, s') \<in> transition M" by (rule exE)
      have "\<exists>p. \<exists> n \<le> (Suc i). p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (p m, act2, p (Suc m)) \<in> transition M)"
      proof
        let ?p = "\<lambda>n. (if n = 0 then s else s')"
        show "\<exists>n \<le> (Suc i). ?p 0 = s \<and> (?p n, act1, ?p (Suc n)) \<in> transition M \<and>
        (\<forall>m<n. (?p m, act2, ?p (Suc m)) \<in> transition M)" using a by auto
      qed
    }
    moreover {
      assume "\<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> (transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e ^^ (Suc i)) {}"
      from this obtain s' where a : "(s, act2, s') \<in> transition M \<and> s' \<in> (transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e ^^ (Suc i)) {}" by (rule exE)
      hence assum1s' : "\<exists>p. \<exists>n \<le> i. p 0 = s' \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (p m, act2, p (Suc m)) \<in> transition M)" using assum1 by auto
      from this obtain p n where b : "n \<le> i \<and> p 0 = s' \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (p m, act2, p (Suc m)) \<in> transition M)" by auto
      have "\<exists>p. \<exists> n \<le> (Suc i). p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (p m, act2, p (Suc m)) \<in> transition M)"
      proof 
        let ?p = "\<lambda>n. (if n = 0 then s else (p (n - 1)))"
        show "\<exists> n \<le> (Suc i). ?p 0 = s \<and> (?p n, act1, ?p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (?p m, act2, ?p (Suc m)) \<in> transition M)" 
        proof
          let ?n = "Suc n"
          have "?n \<le> (Suc i)" using b by auto
          moreover have "?p 0 = s" by auto
          moreover have "(?p ?n, act1, ?p (Suc ?n)) \<in> transition M" using b by auto
          moreover have "(\<forall>m < ?n. (?p m, act2, ?p (Suc m)) \<in> transition M)" using a b less_Suc_eq_0_disj by force
          thus "?n \<le> (Suc i) \<and> ?p 0 = s \<and> (?p ?n, act1, ?p (Suc ?n)) \<in> transition M \<and> (\<forall>m < ?n. (?p m, act2, ?p (Suc m)) \<in> transition M)" using calculation(1) calculation(3) (*wat is dat*) by auto
        qed
      qed
    }
    ultimately show "\<exists>p. \<exists> n \<le> (Suc i). p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m<n. (p m, act2, p (Suc m)) \<in> transition M)" using casesor by auto (*by blast*)
  qed
qed

lemma muX_ordiamondact1ttdiamondact2X_mono [simp] : 
  "mono (transformer (or (diamond act1 tt) (diamond act2 (var 0))) (M :: ('a, 's) lts) e)"
proof
  fix x y :: "'s set"
  assume assum1 : "x \<subseteq> y"
  show "transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e x \<subseteq> transformer (formula.or (diamond act1 tt) (diamond act2 (var 0))) M e y" 
    apply (simp add: newenvironment.cases)
  proof-
    have "{s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> x} \<subseteq> {s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> y}" using assum1 by auto
    thus "{s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> x} \<subseteq> {s. \<exists>s'. (s, act1, s') \<in> transition M} \<union> {s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> y}" by auto
  qed
qed

lemma muX_ordiamondact1ttdiamondact2Xltr [simp] :
  assumes "(finite (UNIV :: 's set))"
  and "(s \<in> formulasemantics (mu (or (diamond act1 tt) (diamond act2 (var 0)))) (M :: ('a, 's) lts) e)"
  shows "(\<exists>p n. p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m < n. (p m, act2, p (Suc m)) \<in> transition M))"
proof-
  have "mono (transformer (or (diamond act1 tt) (diamond act2 (var 0))) M e)" by simp
  hence sinapprox : "s \<in> ((transformer (or (diamond act1 tt) (diamond act2 (var 0))) M e)^^(card (UNIV :: 's set))){}" using assms by simp
  (*note that types in HOL cannot be empty*)
  have "card (UNIV :: 's set) > 0" using assms(1) finite_UNIV_card_ge_0 by auto
  from this obtain i where a : "(card (UNIV :: 's set)) = Suc i" using gr0_implies_Suc by auto
  have "\<exists>p. \<exists>n \<le> i. p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m < n. (p m, act2, p (Suc m)) \<in> transition M)" using existspathlengthi sinapprox a  by auto
  thus ?thesis by auto
qed

lemma muX_ordiamondact1ttdiamondact2Xrtl :
  assumes "(\<exists>p n. p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m < n. (p m, act2, p (Suc m)) \<in> transition M))"
  shows "(s \<in> formulasemantics (mu (or (diamond act1 tt) (diamond act2 (var 0)))) M e)"
  apply (simp add : newenvironment.cases)
proof-
from assms obtain p n where assum1 : "p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m < n. (p m, act2, p (Suc m)) \<in> transition M)" by auto 
  show "\<forall>S'. {s. \<exists>s'. (s, act1, s') \<in> transition M} \<subseteq> S' \<and> {s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> S'} \<subseteq> S' \<longrightarrow> s \<in> S'"
  proof
  fix S'
  show "{s. \<exists>s'. (s, act1, s') \<in> transition M} \<subseteq> S' \<and> {s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> S'} \<subseteq> S' \<longrightarrow> s \<in> S'"
  proof
  assume assum2 : "{s. \<exists>s'. (s, act1, s') \<in> transition M} \<subseteq> S' \<and> {s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> S'} \<subseteq> S'"
  show "s \<in> S'"
  proof (rule ccontr)
    assume assum3 : "s \<notin> S'"
    hence basecase : "(p 0) \<notin> S'" using assum1 by auto
    have "s \<notin> {s. \<exists>s'. (s, act1, s') \<in> transition M} \<and> s \<notin> {s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> S'}" using assum2 assum3 by auto
    have "(\<forall>m \<le> n. p m \<notin> S')"
    proof 
      fix m
      show "(m \<le> n \<longrightarrow> p m \<notin> S')"
        proof (induct_tac m)
          show "0 \<le> n \<longrightarrow> p 0 \<notin> S'" using basecase by auto
        next
          fix m
          assume ih : "m \<le> n \<longrightarrow> p m \<notin> S'"
          have "Suc m \<le> n \<longrightarrow> p (Suc m) \<notin> S'"
          proof
          assume assum4 :  "Suc m \<le> n"
          hence "m < n" by auto
          hence  "p m \<notin> S'" using ih by auto
          hence bl : "(p m) \<notin> {s. \<exists>s'. (s, act2, s') \<in> transition M \<and> s' \<in> S'}" using assum2 by auto
          have "(p m, act2, p (Suc m)) \<in> transition M" using assum1 assum4 by auto
          hence "(p (Suc m)) \<notin> S'" using assum2 bl by auto
          thus "(p (Suc m)) \<notin> S'" using assum2 bl by auto
          qed
        thus "Suc m \<le> n \<longrightarrow> p (Suc m) \<notin> S'" by auto
      qed
    qed
    hence notinS' : "p n \<notin> S'" by auto
    have inS' : "p n \<in> S'" using assum1 assum2 by auto
    thus False using notinS' inS' by auto
  qed
qed
qed
qed

lemma muX_ordiamondact1ttdiamondact2X :
 "(finite (UNIV :: 's set)) \<Longrightarrow> ((s \<in> formulasemantics (mu (or (diamond act1 tt) (diamond act2 (var 0)))) (M :: ('a, 's) lts) e) = 
    (\<exists>p n. p 0 = s \<and> (p n, act1, p (Suc n)) \<in> transition M \<and> (\<forall>m < n. (p m, act2, p (Suc m)) \<in> transition M)))"
  apply (metis muX_ordiamondact1ttdiamondact2Xltr muX_ordiamondact1ttdiamondact2Xrtl)
  done
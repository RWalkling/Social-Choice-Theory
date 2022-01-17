theory SocialWelfareFunction
  imports Main Common Base
begin

(*
  A social welfare function aggregates an entire profile of preferences into a single collective
  preference relation.
*)
type_synonym 'a SWF = "'a PP \<Rightarrow> 'a relation"

abbreviation invalid_swf :: "'a SWF" where "invalid_swf _ \<equiv> \<lambda>_ _. False"

locale social_welfare_function = social_choice_setting +
  fixes g :: "'a SWF"
  assumes g: "preference_profile U n R\<^sub>N \<Longrightarrow> preference_relation U (g R\<^sub>N)"
  assumes g_invalid: "\<not> preference_profile U n R\<^sub>N = (g R\<^sub>N = invalid_swf R\<^sub>N)"
begin

(*
  A group of voters G is decisive for a against b, if, whenever every voter in G has a strict
  preference for a against b, then the collective preference relation also has that preference
*)
definition D\<^sub>G :: "nat set \<Rightarrow> 'a relation"
  where "D\<^sub>G G a b \<equiv> G \<subseteq> N \<and> (\<forall>R\<^sub>N.
      preference_profile U n R\<^sub>N
  \<longrightarrow> (\<forall>i \<in> G. asymm (R\<^sub>N i) a b)
  \<longrightarrow> asymm (g R\<^sub>N) a b)
"

(*
  Semi-decisiveness is a weaker version of decisiveness. It is merely a technical definition needed
  for the proof
*)
definition SD\<^sub>G :: "nat set \<Rightarrow> 'a relation"
  where "SD\<^sub>G G a b \<equiv> G \<subseteq> N \<and> (\<forall>R\<^sub>N.
      preference_profile U n R\<^sub>N
  \<longrightarrow> (\<forall>i \<in> G. asymm (R\<^sub>N i) a b)
    \<and> (\<forall>i \<in> N - G. asymm (R\<^sub>N i) b a)
  \<longrightarrow> asymm (g R\<^sub>N) a b)
"

(* A group of voters is decisive, if it is decisive for every pair of alternatives *)
definition D :: "nat set \<Rightarrow> bool" where "D G \<equiv> G \<subseteq> N \<and> (\<forall>a b. D\<^sub>G G a b)"

lemma d_sd: "D\<^sub>G G a b \<Longrightarrow> SD\<^sub>G G a b" unfolding D\<^sub>G_def SD\<^sub>G_def by auto
lemma D\<^sub>G_trivial: "G \<sqsubseteq> N \<Longrightarrow> D\<^sub>G G a a" unfolding D\<^sub>G_def SD\<^sub>G_def by auto

(* 
  A dictator is a voter who can impose their strict preference onto the whole society.
  That is to say, d is a dictator, iff no matter the preference profile, if d has a strict
  preference for x vs y, then the societal preference will also be to strictly prefer x to y.
*)
abbreviation is_dictator
  where "is_dictator d \<equiv> \<forall>R\<^sub>N x y. preference_profile U n R\<^sub>N \<longrightarrow> (asymm (R\<^sub>N d) x y \<longrightarrow> asymm (g R\<^sub>N) x y)"

end

locale IIA = social_welfare_function +
  assumes IIA: "(\<And>i. R\<^sub>N i x y = R\<^sub>N' i x y) \<Longrightarrow> g R\<^sub>N x y = g R\<^sub>N' x y"

locale pareto = social_welfare_function +
  assumes pareto: "(\<And>i. i \<in> N \<Longrightarrow> asymm (R\<^sub>N i) x y) \<Longrightarrow> asymm (g R\<^sub>N) x y"
begin

lemma "D N" unfolding D_def D\<^sub>G_def using pareto by auto

end

locale dictatorial = social_welfare_function +
  assumes dictatorial: "\<exists>d \<in> N. is_dictator d"

locale at_least_three_alternatives = choice_setting +
  assumes card_U: "3 \<le> card U"

locale dict_3 = dictatorial + at_least_three_alternatives

locale IIA_pareto_3 = IIA + pareto + at_least_three_alternatives
begin

context
  fixes a b c :: 'a and G :: "nat set" 
  assumes GN: "G \<sqsubseteq> N"
  assumes au: "a \<in> U" and bu: "b \<in> U" and cu: "c \<in> U"
  assumes ab: "a \<noteq> b" and ca: "c \<noteq> a" and cb: "c \<noteq> b"
begin

(* Slide 66 top *)
lemma first:
  assumes sdg_ab: "SD\<^sub>G G a b"
  shows "D\<^sub>G G a c"
proof - {
  fix R\<^sub>N :: "'a PP" 
  assume R\<^sub>N_pp: "preference_profile U n R\<^sub>N"
  then interpret re: preference_profile U n R\<^sub>N by auto
  assume G_R\<^sub>N_ac: "i \<in> G \<Longrightarrow> asymm (R\<^sub>N i) a c" for i

  define R1 :: "'a PP" where "R1 \<equiv> \<lambda>i x y. i \<in> N \<and> x \<in> U \<and> y \<in> U \<and> (
    if i \<in> G
      then if y = a then x = a
      else if y = b then x = a \<or> x = b
      else if y = c then x = a \<or> x = b \<or> x = c
      else True
    else if x = b then True
    else if y = b then False
    else R\<^sub>N i x y
  )"

  interpret r1: preference_profile U n R1 proof
    show "\<And>i x y. i \<in> N \<Longrightarrow> x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> R1 i x y" unfolding R1_def by blast
  next
    fix x y z :: 'a and i assume "i \<in> N" "R1 i x y" "R1 i y z"
    interpret pr: preference_relation U "R\<^sub>N i" using \<open>i \<in> N\<close> re.R\<^sub>N by auto
    show "R1 i x z" unfolding R1_def using pr.transitive by (smt (verit, best) R1_def \<open>R1 i x y\<close> \<open>R1 i y z\<close> \<open>i \<in> N\<close> ab cb) next
    show "\<And>i x. i \<in> N \<Longrightarrow> x \<in> U \<Longrightarrow> R1 i x x" unfolding R1_def using R\<^sub>N_pp preference_profile.refl by fastforce 
  next
    fix x y :: 'a and i assume "i \<in> N" "x \<in> U" "y \<in> U"
    interpret pr: preference_relation U "R\<^sub>N i" using \<open>i \<in> N\<close> re.R\<^sub>N by auto
    show "R1 i x y \<or> R1 i y x" unfolding R1_def using pr.complete using \<open>i \<in> N\<close> \<open>x \<in> U\<close> \<open>y \<in> U\<close> by presburger next
    show "\<And>i x y. i \<notin> N \<or> x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> R1 i x y" unfolding R1_def by blast next
  qed

  have "i \<in> G \<Longrightarrow> asymm (R1 i) a b" for i using GN R1_def au ab bu by fastforce
  moreover have "i \<in> N-G \<Longrightarrow> asymm (R1 i) b a" for i using R1_def ab au bu by force
  ultimately have g_R1_ab: "asymm (g R1) a b" using SD\<^sub>G_def r1.preference_profile_axioms sdg_ab by auto

  have "i \<in> N \<Longrightarrow> asymm (R1 i) b c" for i using G_R\<^sub>N_ac R1_def bu cb cu by auto 
  hence g_R1_bc: "asymm (g R1) b c" using pareto by auto 

  interpret gr1: preference_relation U "g R1" by (simp add: g r1.preference_profile_axioms) 

  have g_R1_ac: "asymm (g R1) a c" using g_R1_ab g_R1_bc gr1.transitive by blast

  have agree_on_ac: "R\<^sub>N i a c = R1 i a c" for i using G_R\<^sub>N_ac R1_def ab cb re.R\<^sub>N_domain by auto  
  hence "asymm (g R\<^sub>N) a c" using g_R1_ac IIA[of R\<^sub>N a c R1, OF agree_on_ac] by (smt (verit) G_R\<^sub>N_ac IIA R1_def ab cb re.R\<^sub>N_domain)
} thus "D\<^sub>G G a c" by (simp add: D\<^sub>G_def GN)
qed

lemma first': "G \<sqsubseteq> N \<Longrightarrow> a \<in> U \<Longrightarrow> b \<in> U \<Longrightarrow> a \<noteq> b \<Longrightarrow> D\<^sub>G G a b \<Longrightarrow> c \<in> U \<Longrightarrow> c \<noteq> b \<Longrightarrow> D\<^sub>G G a c" 
  using d_sd first by blast

(* Slide 66 bottom *)
lemma second:
  assumes dg_ab: "D\<^sub>G G a b"
  shows "D\<^sub>G G c b"
proof -
  {
    fix R\<^sub>N :: "'a PP" 
    assume R\<^sub>N_pp: "preference_profile U n R\<^sub>N"
    then interpret re: preference_profile U n R\<^sub>N by auto
    assume G_R\<^sub>N_ab: "i \<in> G \<Longrightarrow> asymm (R\<^sub>N i) c b" for i

    define R :: "'a PP" where "R \<equiv> \<lambda>i x y. i \<in> N \<and> x \<in> U \<and> y \<in> U \<and> (
      if i \<in> G
        then if y = c then x = c
        else if y = a then x = c \<or> x = a
        else if y = b then x = c \<or> x = a \<or> x = b
        else True
      else if y = a then True
      else if x = a then False
      else R\<^sub>N i x y
    )"

    interpret r: preference_profile U n R proof
      show "\<And>i x y. i \<in> N \<Longrightarrow> x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> R i x y" unfolding R_def by blast 
    next
      fix x y z :: 'a and i assume "i \<in> N" "R i x y" "R i y z"
      interpret pr: preference_relation U "R\<^sub>N i" using \<open>i \<in> N\<close> re.R\<^sub>N by auto
      show "R i x z" unfolding R_def using pr.transitive by (smt (z3) R_def \<open>R i x y\<close> \<open>R i y z\<close> \<open>i \<in> N\<close> ab) next
      show "\<And>i x. i \<in> N \<Longrightarrow> x \<in> U \<Longrightarrow> R i x x" unfolding R_def using re.refl by presburger 
    next
      fix x y :: 'a and i assume "i \<in> N" "x \<in> U" "y \<in> U"
      interpret pr: preference_relation U "R\<^sub>N i" using \<open>i \<in> N\<close> re.R\<^sub>N by auto
      show "R i x y \<or> R i y x" unfolding R_def using pr.complete using \<open>i \<in> N\<close> \<open>x \<in> U\<close> \<open>y \<in> U\<close> by presburger next
      show "\<And>i x y. i \<notin> N \<or> x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> R i x y" unfolding R_def by blast next
    qed

    interpret gr: preference_relation U "g R" by (simp add: g r.preference_profile_axioms) 

    have "i \<in> G \<Longrightarrow> asymm (R i) c a" for i using GN R_def au ca cu by fastforce
    moreover have "i \<in> N-G \<Longrightarrow> asymm (R i) c a" for i using R_def ca au cu by force
    ultimately have gr_ca: "asymm (g R) c a" using R_def au pareto by force

    have gr_ab: "asymm (g R) a b" by (smt (verit, del_insts) D\<^sub>G_def G_R\<^sub>N_ab R_def ab au bu dg_ab r.preference_profile_axioms subsetD)
    have gr_cb: "asymm (g R) c b" using gr_ab gr_ca gr.transitive by blast
    have R_agree: "R\<^sub>N i c b = R i c b" for i using G_R\<^sub>N_ab R_def ca ab re.R\<^sub>N_domain by auto 
    have g_R\<^sub>N_cb: "asymm (g R\<^sub>N) c b" using gr_cb IIA[of R\<^sub>N c b R, OF R_agree] by (smt (verit) G_R\<^sub>N_ab IIA R_def ca ab re.R\<^sub>N_domain)
  }
  thus "D\<^sub>G G c b" by (simp add: D\<^sub>G_def GN)
qed

end

(* Slide 66 *)
lemma field_expansion: 
  fixes G
  assumes GN: "G \<sqsubseteq> N"
  assumes semi_decisive: "\<exists>a \<in> U. \<exists>b \<in> U. a \<noteq> b \<and> SD\<^sub>G G a b"
  shows "D G"
proof-
  from semi_decisive obtain a b
    where au: "a \<in> U"
      and bu: "b \<in> U"
      and ab: "a \<noteq> b"
      and sdg_ab: "SD\<^sub>G G a b"
    by auto

  have "U - {a, b} \<noteq> {}" proof (rule ccontr)
    assume "\<not> U - {a, b} \<noteq> {}"
    hence "U = {a, b}" using au bu by auto
    hence "card U = 2" using au bu ab by auto
    thus "False" using card_U by auto
  qed
  then obtain c where cu: "c \<in> U" and ca: "c \<noteq> a" and cb: "c \<noteq> b" by blast

  have dg_ab: "D\<^sub>G G a b" by (metis GN ab au bu ca cb cu first first' sdg_ab) 
  note dg_ac = first[OF GN au bu cu ab ca cb sdg_ab]
  have dg_bc: "D\<^sub>G G b c" using GN au bu ca cb cu dg_ac second by blast 
  have dg_ba: "D\<^sub>G G b a" using GN au bu ab cb ca cu dg_bc first' by blast

  {
    fix x y R\<^sub>N 
    assume R\<^sub>N_pp: "preference_profile U n R\<^sub>N" 
    assume G_agree_xy: "i \<in> G \<Longrightarrow> asymm (R\<^sub>N i) x y" for i
    have dg_by: "D\<^sub>G G b y" by (metis D\<^sub>G_def GN cb cu d_sd dg_ab dg_ba dg_bc first preference_profile.R\<^sub>N_domain) 
    have "asymm (g R\<^sub>N) x y" by (smt (verit, ccfv_threshold) D\<^sub>G_def GN G_agree_xy R\<^sub>N_pp ab au bu dg_ab dg_by ex_min_if_finite filled_G preference_profile.R\<^sub>N_domain second)
  }
  thus "D G" by (simp add: GN social_welfare_function.D\<^sub>G_def social_welfare_function.D_def social_welfare_function_axioms) 
qed

context
  fixes G :: "nat set"
  assumes GN: "G \<sqsubseteq> N"
  assumes G_decisive: "D G"
begin

(*
  Lemma: When partitioning a decisive group into two nonempty groups, then at least one of them is
  decisive as well.
*)
lemma split_decisive:
  fixes G\<^sub>1 G\<^sub>2 :: "nat set"
  assumes G\<^sub>1G: "G\<^sub>1 \<sqsubseteq> G" 
      and G\<^sub>2G: "G\<^sub>2 \<sqsubseteq> G"
      and disjoint: "G\<^sub>1 \<inter> G\<^sub>2 = {}"
      and cover: "G\<^sub>1 \<union> G\<^sub>2 = G"
    shows "D G\<^sub>1 \<or> D G\<^sub>2"
proof -
  have G\<^sub>1N: "G\<^sub>1 \<sqsubseteq> N" using GN G\<^sub>1G by auto
  have G\<^sub>2N: "G\<^sub>2 \<sqsubseteq> N" using GN G\<^sub>2G by auto

  have "U \<noteq> {}" using nonempty_universe by auto
  then obtain a where au: "a \<in> U" by auto

  have "U \<noteq> {a}" using card_U by auto
  then obtain b where bu: "b \<in> U" and ab: "a \<noteq> b" using au by auto

  have "U \<noteq> {a, b}" using card_U au bu ab by auto
  then obtain c where cu: "c \<in> U" and ca: "c \<noteq> a" and bc: "b \<noteq> c" using au bu ab by auto

  define G\<^sub>1_rel :: "'a relation" where "G\<^sub>1_rel \<equiv> \<lambda>x y. x \<in> U \<and> y \<in> U \<and> (
    if y = a then x = a else
    if y = b then x = a \<or> x = b else
    if y = c then x = a \<or> x = b \<or> x = c else
    True
  )"
  interpret G\<^sub>1_pref: preference_relation U G\<^sub>1_rel 
    apply unfold_locales unfolding G\<^sub>1_rel_def apply blast apply metis apply simp apply presburger done

  define G\<^sub>2_rel :: "'a relation" where "G\<^sub>2_rel \<equiv> \<lambda>x y. x \<in> U \<and> y \<in> U \<and> (
    if y = b then x = b else
    if y = c then x = b \<or> x = c else
    if y = a then x = b \<or> x = c \<or> x = a else
    True
  )"
  interpret G\<^sub>2_pref: preference_relation U G\<^sub>2_rel
    apply unfold_locales unfolding G\<^sub>2_rel_def apply blast apply metis apply simp apply presburger done

  define NG_rel :: "'a relation" where "NG_rel \<equiv> \<lambda>x y. x \<in> U \<and> y \<in> U \<and> (
    if y = c then x = c else
    if y = a then x = c \<or> x = a else
    if y = b then x = c \<or> x = a \<or> x = b else
    True
  )"
  interpret NG_pref: preference_relation U NG_rel
    apply unfold_locales unfolding NG_rel_def apply blast apply metis apply simp apply presburger done

  define R :: "nat set \<Rightarrow> nat set \<Rightarrow> 'a PP" where "R \<equiv> \<lambda>G\<^sub>1 G\<^sub>2 i x y. x \<in> U \<and> y \<in> U \<and> (
    if i \<in> G\<^sub>1 then G\<^sub>1_rel x y else
    if i \<in> G\<^sub>2 then G\<^sub>2_rel x y else
    if i \<in> N then NG_rel x y else
    False
  )"

  interpret R_pp: preference_profile U n "R G\<^sub>1 G\<^sub>2" proof unfold_locales
    show "\<And>i x y. i \<in> N \<Longrightarrow> x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> R G\<^sub>1 G\<^sub>2 i x y" using R_def by blast 
  next
    fix x y z :: 'a and i assume "i \<in> N" "R G\<^sub>1 G\<^sub>2 i x y" "R G\<^sub>1 G\<^sub>2 i y z"
    thus "R G\<^sub>1 G\<^sub>2 i x z" unfolding R_def by (metis (no_types, lifting) G\<^sub>1_pref.transitive G\<^sub>2_pref.transitive NG_pref.transitive) next
    show "\<And>i x. i \<in> N \<Longrightarrow> x \<in> U \<Longrightarrow> R G\<^sub>1 G\<^sub>2 i x x" unfolding R_def using G\<^sub>1_pref.reflexive G\<^sub>2_pref.reflexive NG_pref.reflexive by auto 
  next
    fix x y :: 'a and i assume "i \<in> N" "x \<in> U" "y \<in> U"
    thus "R G\<^sub>1 G\<^sub>2 i x y \<or> R G\<^sub>1 G\<^sub>2 i y x" unfolding R_def using G\<^sub>1_pref.complete G\<^sub>2_pref.complete NG_pref.complete by auto next
    show "\<And>i x y. i \<notin> N \<or> x \<notin> U \<or> y \<notin> U \<Longrightarrow> \<not> R G\<^sub>1 G\<^sub>2 i x y" by (metis G\<^sub>1N G\<^sub>2N R_def psubsetD psubsetI)
  qed
  interpret g_R_pr: preference_relation U "g (R G\<^sub>1 G\<^sub>2)" using g[OF R_pp.preference_profile_axioms] .

  have G\<^sub>1_bc: "i \<in> G\<^sub>1 \<Longrightarrow> asymm (R G\<^sub>1 G\<^sub>2 i) b c" for i using G\<^sub>1_rel_def R_def bc bu ca cu by auto
  have G\<^sub>2_bc: "i \<in> G\<^sub>2 \<Longrightarrow> asymm (R G\<^sub>1 G\<^sub>2 i) b c" for i using G\<^sub>1_bc G\<^sub>2_rel_def R_def bc bu cu by auto
  have G_bc: "i \<in> G \<Longrightarrow> asymm (R G\<^sub>1 G\<^sub>2 i) b c" for i using cover G\<^sub>1_bc G\<^sub>2_bc by blast
  have g_bc: "asymm (g (R G\<^sub>1 G\<^sub>2)) b c" using G_decisive R_pp.preference_profile_axioms D\<^sub>G_def D_def G_bc by auto

  show "D G\<^sub>1 \<or> D G\<^sub>2" proof (cases "g (R G\<^sub>1 G\<^sub>2) c a")
    case True
    hence g_ba: "asymm (g (R G\<^sub>1 G\<^sub>2)) b a" by (metis R_pp.preference_profile_axioms g g_bc preference_relation.axioms(1) transitive_preference.transitive)
    have sdg_G\<^sub>2_ba: "SD\<^sub>G G\<^sub>2 b a" unfolding SD\<^sub>G_def proof
      show "G\<^sub>2 \<subseteq> N" using GN G\<^sub>2N by auto next
      {
        fix R\<^sub>N assume "preference_profile U n R\<^sub>N" 
        then interpret R\<^sub>N_pp: preference_profile U n R\<^sub>N .

        assume assm: "(\<forall>i\<in>G\<^sub>2. asymm (R\<^sub>N i) b a) \<and> (\<forall>i\<in>N - G\<^sub>2. asymm (R\<^sub>N i) a b)"
        hence in_G\<^sub>2: "i\<in>G\<^sub>2 \<Longrightarrow> asymm (R\<^sub>N i) b a" for i by auto

        have RG\<^sub>2_ba: "i \<in> G\<^sub>2 \<Longrightarrow> asymm (R G\<^sub>1 G\<^sub>2 i) b a" for i unfolding R_def G\<^sub>2_rel_def by (smt (z3) IntI R\<^sub>N_pp.R\<^sub>N_domain disjoint empty_iff in_G\<^sub>2)
        have R_not_G\<^sub>2_ab: "i \<in> N-G\<^sub>2 \<Longrightarrow> asymm (R G\<^sub>1 G\<^sub>2 i) a b" for i unfolding R_def G\<^sub>1_rel_def NG_rel_def using ab au bc bu by auto
        have R\<^sub>N_G\<^sub>2_ba: "i \<in> G\<^sub>2 \<Longrightarrow> asymm (R\<^sub>N i) b a" for i by (smt (z3) IntI R\<^sub>N_pp.R\<^sub>N_domain disjoint empty_iff in_G\<^sub>2)
        have R\<^sub>N_not_G\<^sub>2_ba: "i \<in> N-G\<^sub>2 \<Longrightarrow> asymm (R\<^sub>N i) a b" for i using assm by auto 

        have "asymm (g R\<^sub>N) b a = asymm (g (R G\<^sub>1 G\<^sub>2)) b a" by (metis Diff_iff IIA R\<^sub>N_pp.R\<^sub>N_domain R_pp.R\<^sub>N_domain RG\<^sub>2_ba R_not_G\<^sub>2_ab assm g_ba in_G\<^sub>2) 
        hence "asymm (g R\<^sub>N) b a" using g_ba by simp
      }
      thus "\<forall>R\<^sub>N. preference_profile U n R\<^sub>N \<longrightarrow> (\<forall>i\<in>G\<^sub>2. asymm (R\<^sub>N i) b a) \<and> (\<forall>i\<in>N - G\<^sub>2. asymm (R\<^sub>N i) a b) \<longrightarrow> asymm (g R\<^sub>N) b a " by auto
    qed
    show ?thesis by (metis G\<^sub>2N sdg_G\<^sub>2_ba ab au bu field_expansion) 
  next
    case False
    hence g_ca: "asymm (g (R G\<^sub>1 G\<^sub>2)) a c" using g_R_pr.complete au cu by blast

    have sdg_G\<^sub>1ac: "SD\<^sub>G G\<^sub>1 a c" unfolding SD\<^sub>G_def proof
      show "G\<^sub>1 \<subseteq> N" using GN G\<^sub>1N by auto next
      {
        fix R\<^sub>N
        assume "preference_profile U n R\<^sub>N"
        then interpret R\<^sub>N_pp: preference_profile U n R\<^sub>N .
        assume assm: "(\<forall>i\<in>G\<^sub>1. asymm (R\<^sub>N i) a c) \<and> (\<forall>i\<in>N - G\<^sub>1. asymm (R\<^sub>N i) c a)"
        hence in_G\<^sub>1: "i\<in>G\<^sub>1 \<Longrightarrow> asymm (R\<^sub>N i) a c" for i by auto

        have RG\<^sub>1_ac: "i \<in> G\<^sub>1 \<Longrightarrow> asymm (R G\<^sub>1 G\<^sub>2 i) a c" for i unfolding R_def G\<^sub>1_rel_def by (smt (z3) IntI R\<^sub>N_pp.R\<^sub>N_domain disjoint empty_iff in_G\<^sub>1)
        have R_not_G\<^sub>1_ca: "i \<in> N-G\<^sub>1 \<Longrightarrow> asymm (R G\<^sub>1 G\<^sub>2 i) c a" for i unfolding R_def G\<^sub>1_rel_def NG_rel_def using ab au bc bu G\<^sub>2_rel_def ca cu by force 
        have R\<^sub>N_G\<^sub>1_ac: "i \<in> G\<^sub>1 \<Longrightarrow> asymm (R\<^sub>N i) a c" for i by (smt (z3) IntI R\<^sub>N_pp.R\<^sub>N_domain disjoint empty_iff in_G\<^sub>1)
        have R\<^sub>N_not_G\<^sub>1_ac: "i \<in> N-G\<^sub>1 \<Longrightarrow> asymm (R\<^sub>N i) c a" for i using assm by auto

        have "asymm (g R\<^sub>N) a c = asymm (g (R G\<^sub>1 G\<^sub>2)) a c" by (metis Diff_iff IIA R\<^sub>N_pp.R\<^sub>N_domain R_pp.R\<^sub>N_domain RG\<^sub>1_ac R_not_G\<^sub>1_ca assm g_ca in_G\<^sub>1)
        hence "asymm (g R\<^sub>N) a c" using g_ca by simp
      }
      thus "\<forall>R\<^sub>N. preference_profile U n R\<^sub>N \<longrightarrow> (\<forall>i\<in>G\<^sub>1. asymm (R\<^sub>N i) a c) \<and> (\<forall>i\<in>N - G\<^sub>1. asymm (R\<^sub>N i) c a) \<longrightarrow> asymm (g R\<^sub>N) a c" by auto
    qed
    show ?thesis by (metis G\<^sub>1N au ca cu field_expansion sdg_G\<^sub>1ac)
  qed
qed

(* 
  Partition a decisive group G into nonempty blocks and use the above theorem to show that therefore
  G has a decisive subset.
*)
lemma decisive_subset:
  assumes "card G \<noteq> 1"
  shows "\<exists>G' \<subset> G. G' \<noteq> {} \<and> D G'"
proof -
  have "filled G" using GN filled_G by auto

  obtain g where "g \<in> G" using \<open>filled G\<close> by auto
  define G\<^sub>1 :: "nat set" where "G\<^sub>1 \<equiv> {g}"
  define G\<^sub>2 :: "nat set" where "G\<^sub>2 \<equiv> G - {g}"

  have "card G - 1 \<le> card G\<^sub>2" using G\<^sub>2_def by (metis \<open>filled G\<close> \<open>g \<in> G\<close> card_Diff_singleton order_eq_iff)
  hence "G\<^sub>2 \<noteq> {}" using \<open>card G \<noteq> 1\<close> \<open>filled G\<close> by (metis G\<^sub>2_def \<open>g \<in> G\<close> insert_Diff is_singletonI is_singleton_altdef)

  have "G\<^sub>1 \<sqsubseteq> G" unfolding G\<^sub>1_def by (simp add: \<open>g \<in> G\<close>)
  moreover have "G\<^sub>2 \<sqsubseteq> G" unfolding G\<^sub>2_def using G\<^sub>2_def \<open>G\<^sub>2 \<noteq> {}\<close> by blast 
  moreover have "G\<^sub>1 \<inter> G\<^sub>2 = {}" unfolding G\<^sub>1_def G\<^sub>2_def using G\<^sub>2_def \<open>G\<^sub>2 \<noteq> {}\<close> by blast
  moreover have "G\<^sub>1 \<union> G\<^sub>2 = G" unfolding G\<^sub>1_def G\<^sub>2_def using \<open>g \<in> G\<close> by auto 
  ultimately have "D G\<^sub>1 \<or> D G\<^sub>2" using split_decisive by metis 

  thus ?thesis proof
    assume "D G\<^sub>1"
    hence "G\<^sub>1 \<subset> G \<and> (filled G) \<and> G\<^sub>1 \<sqsubseteq> N \<and> D G\<^sub>1" using D_def G\<^sub>1_def G\<^sub>2_def \<open>D G\<^sub>1\<close> \<open>G\<^sub>1 \<sqsubseteq> G\<close> \<open>G\<^sub>2 \<sqsubseteq> G\<close> \<open>filled G\<close> by auto
    thus ?thesis using finite_subset by auto
  next
    assume "D G\<^sub>2"
    have "G\<^sub>2 \<subset> G \<and> (filled G) \<and> G\<^sub>2 \<sqsubseteq> N \<and> D G\<^sub>2" using G\<^sub>2_def \<open>D G\<^sub>2\<close> \<open>G \<sqsubseteq> N\<close> \<open>D G\<close> \<open>G\<^sub>2 \<sqsubseteq> G\<close> \<open>filled G\<close> \<open>g \<in> G\<close> by blast
    thus ?thesis using finite_subset by auto
  qed
qed

end

end

(* Arrows impossibility theorem *)
(*
  We take a decisive group (here the group N of all voters is decisive because of pareto
  optimality) and keep splitting it until we arrive at a decisive group of a single voter. That
  voter is therefore a dictator.
*)
sublocale IIA_pareto_3 \<subseteq> dictatorial proof(unfold_locales)
  (* The invariant *)
  define P where "P \<equiv> \<lambda>G. G \<sqsubseteq> N \<and> D G"

  have initial: "P N" unfolding P_def D\<^sub>G_def D_def using pareto by (metis empty_iff subset_refl)
  have step: "P s \<and> s \<sqsubseteq> N \<and> card s \<noteq> 1 \<Longrightarrow> \<exists>G'. P G' \<and> G' \<subseteq> N \<and> G' \<noteq> {} \<and> G' \<subset> s" for s unfolding P_def using decisive_subset by (metis D_def)

  obtain d where "d \<in> N" "D {d}" using subset_descent[of N P, OF filled_N initial, simplified, OF step] P_def by auto
  hence "D\<^sub>G {d} a b" for a b unfolding D_def by auto
  hence "preference_profile U n R\<^sub>N \<longrightarrow> (\<forall>i \<in> {d}. asymm (R\<^sub>N i) a b) \<longrightarrow> asymm (g R\<^sub>N) a b" for R\<^sub>N a b unfolding D\<^sub>G_def by auto
  thus "\<exists>d \<in> N. is_dictator d" using \<open>d \<in> N\<close> by auto
qed

end
import ClassicalLogicLean.NV.Sub.Var.All.Rec.Sub


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


namespace FOL.NV.Sub.Pred.All.Rec.Option.Fresh

open Formula_


def pred_var_free_var_set
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_)) :=
  fun ((X : PredName_), (n : ℕ)) =>
    let opt := τ X n
    if h : Option.isSome opt
    then
      let val := Option.get opt h
      let zs := val.fst
      let H := val.snd
      H.free_var_set \ zs.toFinset
    else ∅


def sub_pred_all_rec_opt_aux
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (σ : VarName_ → VarName_) :
  Formula_ → Formula_
  | pred_const_ X xs => pred_const_ X (xs.map σ)
  | pred_var_ X xs =>
      let opt := τ X xs.length
      if h : Option.isSome opt
      then
        let val := Option.get opt h
        let zs := val.fst
        let H := val.snd
        if xs.length = zs.length
        then Sub.Var.All.Rec.Fresh.sub_var_all_rec (Function.updateFromPairOfListsITE id zs (xs.map σ)) c H
        else pred_var_ X (xs.map σ)
      else pred_var_ X (xs.map σ)
  | eq_ x y => eq_ (σ x) (σ y)
  | true_ => true_
  | false_ => false_
  | not_ phi =>
      not_ (sub_pred_all_rec_opt_aux c τ σ phi)
  | imp_ phi psi =>
      imp_
      (sub_pred_all_rec_opt_aux c τ σ phi)
      (sub_pred_all_rec_opt_aux c τ σ psi)
  | and_ phi psi =>
      and_
      (sub_pred_all_rec_opt_aux c τ σ phi)
      (sub_pred_all_rec_opt_aux c τ σ psi)
  | or_ phi psi =>
      or_
      (sub_pred_all_rec_opt_aux c τ σ phi)
      (sub_pred_all_rec_opt_aux c τ σ psi)
  | iff_ phi psi =>
      iff_
      (sub_pred_all_rec_opt_aux c τ σ phi)
      (sub_pred_all_rec_opt_aux c τ σ psi)
  | forall_ x phi =>
      let S : Finset VarName_ := (Finset.image (Function.updateITE σ x x) (free_var_set phi) ∪ Finset.biUnion (pred_var_set phi) (pred_var_free_var_set τ))

      let x' : VarName_ :=
        if x ∈ S
        then fresh x c S
        else x

      forall_ x' (sub_pred_all_rec_opt_aux c τ (Function.updateITE σ x x') phi)
  | exists_ x phi =>
      let S : Finset VarName_ := (Finset.image (Function.updateITE σ x x) (free_var_set phi) ∪ Finset.biUnion (pred_var_set phi) (pred_var_free_var_set τ))

      let x' : VarName_ :=
        if x ∈ S
        then fresh x c S
        else x

      exists_ x' (sub_pred_all_rec_opt_aux c τ (Function.updateITE σ x x') phi)
  | def_ X xs => def_ X (xs.map σ)


def sub_pred_all_rec_opt
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (F : Formula_) :
  Formula_ :=
  sub_pred_all_rec_opt_aux c τ id F


def Interpretation_.using_pred
  (D : Type)
  (I : Interpretation_ D)
  (pred_ : PredName_ → List D → Prop) :
  Interpretation_ D := {
    nonempty := I.nonempty
    pred_const_ := I.pred_const_
    pred_var_ := pred_ }


def I'
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_)) :
  Interpretation_ D :=
  (Interpretation_.using_pred D I (
  fun (X : PredName_) (ds : List D) =>
  let opt := τ X ds.length
  if h : Option.isSome opt
  then
    let val := Option.get opt h
    let zs := val.fst
    let H := val.snd
    if ds.length = zs.length
    then holds D I (Function.updateFromPairOfListsITE V zs ds) E H
    else I.pred_var_ X ds
  else I.pred_var_ X ds) )


theorem substitution_theorem_sub_pred_all_rec_opt_aux
  (D : Type)
  (I : Interpretation_ D)
  (V V' V'' : Valuation_ D)
  (E : Env_)
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (σ : VarName_ → VarName_)
  (F : Formula_)
  (h1 : ∀ (x : VarName_), var_is_free_in x F → V' x = V (σ x))
  (h2 : ∀ (x : VarName_), x ∈ F.pred_var_set.biUnion (pred_var_free_var_set τ) → V'' x = V x) :
  holds D (I' D I V'' E τ) V' E F ↔ holds D I V E (sub_pred_all_rec_opt_aux c τ σ F) :=
  by
  induction F generalizing V V' σ
  case pred_const_ X xs =>
    simp only [var_is_free_in] at h1

    simp only [sub_pred_all_rec_opt_aux]
    simp only [holds]
    simp only [I']
    simp only [Interpretation_.using_pred]
    simp only [List.map_map]
    congr! 1
    simp only [List.map_eq_map_iff]
    intro x a1
    simp only [Function.comp_apply]
    exact h1 x a1
  case pred_var_ X xs =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2
    simp only [Finset.singleton_biUnion] at h2
    simp only [pred_var_free_var_set] at h2

    simp only [sub_pred_all_rec_opt_aux]
    simp only [holds]
    simp only [I']
    simp only [Interpretation_.using_pred]
    simp only [List.length_map]
    split
    case isTrue c1 =>
      split
      case isTrue c2 =>
        simp only [c1] at h2
        split at h2
        case isTrue c3 =>
          simp only [Finset.mem_sdiff, List.mem_toFinset] at h2

          set zs := (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).1

          set H := (Option.get (τ X (List.length xs)) (_ : Option.isSome (τ X (List.length xs)) = true)).2

          obtain s1 := Sub.Var.All.Rec.Fresh.substitution_theorem_sub_var_all_rec D I V E (Function.updateFromPairOfListsITE id zs (xs.map σ)) c H
          simp only [Function.updateFromPairOfListsITE_comp] at s1

          simp only [CompTriple.comp_eq, List.map_map] at s1
          rewrite [s1]
          clear s1

          apply holds_coincide_var
          intro x a1
          by_cases c4 : x ∈ zs
          · apply Function.updateFromPairOfListsITE_map_mem_ext
            · simp only [Function.comp_apply]
              exact h1
            · simp only [← c2]
            · exact c4
          · simp only [Function.updateFromPairOfListsITE_not_mem V'' x zs (List.map V' xs) c4]
            simp only [Function.updateFromPairOfListsITE_not_mem V x zs (List.map (V ∘ σ ) xs) c4]
            apply h2
            simp only [var_is_free_in_iff_mem_free_var_set] at a1
            exact ⟨a1, c4⟩
        case isFalse c3 =>
          exfalso
          apply c3
          exact True.intro
      case isFalse c2 =>
        simp only [holds]
        simp only [List.map_map]
        congr! 1
        simp only [List.map_eq_map_iff]
        intro x a1
        simp only [Function.comp_apply]
        exact h1 x a1
    case isFalse c1 =>
      simp only [holds]
      simp only [List.map_map]
      congr! 1
      simp only [List.map_eq_map_iff]
      intro x a1
      simp only [Function.comp_apply]
      exact h1 x a1
  case eq_ x y =>
    simp only [var_is_free_in] at h1

    simp only [sub_pred_all_rec_opt_aux]
    simp only [holds]

    have s1 : V' x = V (σ x) :=
    by
      apply h1
      left
      apply Eq.refl
    rewrite [s1]

    have s2 : V' y = V (σ y) :=
    by
      apply h1
      right
      apply Eq.refl
    rewrite [s2]

    apply Iff.refl
  case true_ | false_ =>
    simp only [sub_pred_all_rec_opt_aux]
    simp only [holds]
  case not_ phi phi_ih =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2

    simp only [sub_pred_all_rec_opt_aux]
    simp only [holds]
    congr! 1
    exact phi_ih V V' σ h1 h2
  case
      imp_ phi psi phi_ih psi_ih
    | and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2

    simp only [sub_pred_all_rec_opt_aux]
    simp only [holds]
    congr! 1
    · apply phi_ih V V' σ
      · intro x a1
        apply h1
        left
        exact a1
      · intro x a1
        apply h2
        simp only [Finset.mem_biUnion] at a1
        obtain ⟨a, a1_left, a1_right⟩ := a1

        simp only [Finset.mem_biUnion, Finset.mem_union]
        apply Exists.intro a
        tauto
    · apply psi_ih V V' σ
      · intro x a1
        apply h1
        right
        exact a1
      · intro x a1
        apply h2
        simp only [Finset.mem_biUnion] at a1
        obtain ⟨a, a1_left, a1_right⟩ := a1

        simp only [Finset.mem_biUnion, Finset.mem_union]
        apply Exists.intro a
        tauto
  case forall_ x phi ih | exists_ x phi ih =>
    simp only [var_is_free_in] at h1

    simp only [pred_var_set] at h2

    simp only [sub_pred_all_rec_opt_aux]
    simp only [I']
    simp only [Interpretation_.using_pred]
    simp only [holds]

    first | apply forall_congr' | apply exists_congr
    intro d

    apply ih
    · intro v a1
      split
      case isTrue c1 =>
        simp only [Function.updateITE]
        split
        case isTrue c2 =>
          split
          case isTrue c3 =>
            apply Eq.refl
          case isFalse c3 =>
            contradiction
        case isFalse c2 =>
          split
          case isTrue c3 =>
            obtain s1 := fresh_not_mem x c ((Finset.image (Function.updateITE σ x x) (free_var_set phi)) ∪ (Finset.biUnion (pred_var_set phi) (pred_var_free_var_set τ)))
            simp only [← c3] at s1
            simp only [Finset.mem_union] at s1

            simp only [var_is_free_in_iff_mem_free_var_set] at a1

            obtain s2 := Finset.mem_image_of_mem (Function.updateITE σ x x) a1
            simp only [Function.updateITE] at s2
            simp only [if_neg c2] at s2

            exfalso
            apply s1
            left
            exact s2
          case isFalse c3 =>
            apply h1
            tauto
      case isFalse c1 =>
        simp only [Function.updateITE]
        split
        case isTrue c2 =>
          split
          case isTrue c3 =>
            apply Eq.refl
          case isFalse c3 =>
            contradiction
        case isFalse c2 =>
          split
          case isTrue c3 =>
            obtain s1 := Sub.Var.All.Rec.Fresh.sub_var_all_rec_free_var_set_eq_free_var_set_image (Function.updateITE σ x x) c phi

            simp only [var_is_free_in_iff_mem_free_var_set] at a1

            obtain s2 := Finset.mem_image_of_mem (Function.updateITE σ (σ v) (σ v)) a1
            simp only [Function.updateITE] at s2

            split at s2
            case isTrue c4 =>
              rewrite [c4] at c2
              contradiction
            case isFalse c4 =>
              simp only [← c3] at c1
              simp only [Finset.mem_union] at c1
              rewrite [not_or] at c1
              obtain ⟨c1_left, c1_right⟩ := c1
              contradiction
          case isFalse c3 =>
            apply h1
            tauto
    · intro v a1
      split
      case isTrue c1 =>
        simp only [Function.updateITE]
        split
        case isTrue c2 =>
          obtain s1 := Sub.Var.All.Rec.Fresh.sub_var_all_rec_free_var_set_eq_free_var_set_image (Function.updateITE σ x x) c phi
          simp only [← s1] at c2

          obtain s2 := fresh_not_mem x c ((free_var_set (Var.All.Rec.Fresh.sub_var_all_rec (Function.updateITE σ x x) c phi)) ∪ (Finset.biUnion (pred_var_set phi) (pred_var_free_var_set τ)))
          simp only [← c2] at s2
          simp only [Finset.mem_union] at s2

          rewrite [not_or] at s2
          obtain ⟨s2_left, s2_right⟩ := s2
          contradiction
        case isFalse c2 =>
          exact h2 v a1
      case isFalse c1 =>
        simp only [Finset.mem_union] at c1
        rewrite [not_or] at c1
        obtain ⟨c1_left, c1_right⟩ := c1
        have s1 : ¬ v = x :=
        by
          intro contra
          apply c1_right
          rewrite [← contra]
          exact a1

        simp only [Function.updateITE]
        split
        case isTrue c2 =>
          contradiction
        case isFalse c2 =>
          exact h2 v a1
  case def_ X xs =>
    simp only [sub_pred_all_rec_opt_aux]

    induction E generalizing V V' σ
    case nil =>
      simp only [holds]
    case cons E_hd E_tl E_ih =>
      simp only [var_is_free_in] at h1

      simp only [holds]

      have s1 : (List.map V' xs) = (List.map (V ∘ σ) xs) :=
      by
        simp only [List.map_eq_map_iff]
        intro x a1
        exact h1 x a1
      simp only [s1]

      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          have s2 : holds D I (Function.updateFromPairOfListsITE V' E_hd.args (List.map (V ∘ σ) xs)) E_tl E_hd.q ↔ holds D I (Function.updateFromPairOfListsITE V E_hd.args (List.map (V ∘ σ) xs)) E_tl E_hd.q :=
          by
            apply holds_coincide_var
            intro x a1
            apply Function.updateFromPairOfListsITE_map_mem_ext
            · simp only [Function.comp_apply]
              intro y a2
              exact True.intro
            · tauto
            · simp only [var_is_free_in_iff_mem_free_var_set] at a1
              simp only [← List.mem_toFinset]
              apply Finset.mem_of_subset E_hd.h1 a1

          simp only [List.map_map]
          simp only [← s2]

          apply holds_coincide_pred_var
          · simp only [I']
            simp only [Interpretation_.using_pred]
          · intro P ds a1
            simp only [pred_var_occurs_in_iff_mem_pred_var_set] at a1
            simp only [E_hd.h2] at a1
            simp at a1
        case isFalse c2 =>
          simp only [List.length_map] at c2
          contradiction
      case isFalse c1 =>
        obtain s2 := E_ih V V' σ
        simp only [var_is_free_in] at s2
        specialize s2 h1 h2
        simp only [← s2]
        split
        case isTrue c2 =>
          simp only [List.length_map] at c2
          contradiction
        case isFalse c2 =>
          apply holds_coincide_pred_var
          · simp only [I']
            simp only [Interpretation_.using_pred]
          · intro P ds a1
            simp only [pred_var_occurs_in] at a1


theorem substitution_theorem_sub_pred_all_rec_opt
  (D : Type)
  (I : Interpretation_ D)
  (V : Valuation_ D)
  (E : Env_)
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (F : Formula_) :
  holds D (I' D I V E τ) V E F ↔ holds D I V E (sub_pred_all_rec_opt c τ F) :=
  by
  apply substitution_theorem_sub_pred_all_rec_opt_aux
  · intro x a1
    simp only [id_eq]
  · intro x a1
    apply Eq.refl


theorem substitution_is_valid_sub_pred_all_rec_opt
  (c : Char)
  (τ : PredName_ → ℕ → Option (List VarName_ × Formula_))
  (F : Formula_)
  (h1 : is_valid F) :
  is_valid (sub_pred_all_rec_opt c τ F) :=
  by
  simp only [is_valid] at h1

  simp only [is_valid]
  intro D I V E
  simp only [← substitution_theorem_sub_pred_all_rec_opt]
  apply h1


end FOL.NV.Sub.Pred.All.Rec.Option.Fresh

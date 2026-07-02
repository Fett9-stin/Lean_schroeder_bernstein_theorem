import Mathlib.Tactic
import Mathlib.Data.Set.Function
open Function
open Set

----------------------------setting----------------------------------------
noncomputable section
open Classical
variable {α β : Type*}
variable (x : α)
variable {I : Type*} (A : I → Set α)
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n
---------------------------setting------------------------------------------------------

------------------------the theorem i really dont wanna prove----------------------------
theorem BijOn_invFun {α β : Type*} [Nonempty α] {f : α → β} {A : Set α} {B : Set β}
    (h : BijOn f A B) : BijOn (invFunOn f A) B A := by 
    refine ⟨h.surjOn.mapsTo_invFunOn, h.surjOn.injOn_invFunOn, ?_⟩
    intro x hx
    use f x
    exact ⟨h.mapsTo hx, h.injOn.leftInvOn_invFunOn hx⟩
  /--/  
     ---copilot provides me the wrong definition!!with invFun f
  refine ⟨?maps, ?inj, ?surj⟩
  -- MapsTo: for all y ∈ B, invFunOn f A y ∈ A
  · intro y hy
    have : ∃ x ∈ A, f x = y := h.surjOn hy
    rw [invFunOn]
    split_ifs
    · exact (Classical.choose_spec this).1

  -- InjOn: if invFunOn f A y₁ = invFunOn f A y₂, then y₁ = y₂
  · intro y₁ hy₁ y₂ hy₂ heq
    let ex₁ := h.surjOn hy₁
    let ex₂ := h.surjOn hy₂
    have eq₁ : f (invFunOn f A y₁) = y₁ := by
      rw [invFunOn]
      split_ifs with h'
      · exact (Classical.choose_spec h').2
      · exfalso; exact h' ex₁
    have eq₂ : f (invFunOn f A y₂) = y₂ := by
      rw [invFunOn]
      split_ifs with h'
      · exact (Classical.choose_spec h').2
      · exfalso; exact h' ex₂
    -- f (invFunOn f A y₁) = y₁ and f (invFunOn f A y₂) = y₂, and invFunOn f A y₁ = invFunOn f A y₂ =⇒ y₁ = y₂
    rw [← eq₁, ← eq₂, heq]

  -- SurjOn: for all x ∈ A, ∃ y ∈ B, invFunOn f A y = x
  · intro x hxA
    use f x
    constructor
    · exact h.mapsTo hxA
    · rw [invFunOn]
      split_ifs with h'
      · have key := Classical.choose_spec h'
        -- key : ∃ (x : α), x ∈ A ∧ f x = f x
        -- so (Classical.choose h') ∈ A ∧ f (Classical.choose h') = f x
        have eq_fx : f (Classical.choose h') = f x := key.2
        have inA : (Classical.choose h') ∈ A := key.1
        have : Classical.choose h' = x := h.injOn inA hxA eq_fx
        rw [this]
      · exfalso; exact h' ⟨x, hxA, rfl⟩
-/

------------------------the theorem i really dont wanna prove------------------------------------

-------------------------theorem for two bijections on disjoint sets ----------------------------------------
theorem bijective_disjoint {α β : Type*}[Nonempty β] {A1 A2 : Set α} {B1 B2 : Set β}   ---- little bit easier in proving h is injective
    {f : α → β} {g : β → α}
    (h1 : BijOn f A1 B1) (h2 : BijOn g B2 A2)
    (h3 : A1 ∪ A2 = univ ∧ A1 ∩ A2 = ∅ ) (h4 : B1 ∪ B2 = univ ∧ B1 ∩ B2 =∅ ) :
  ∃ h : α → β, Bijective h := by
  -- Define the glued function
  let h : α → β := fun x => if x ∈ A1 then f x else (invFunOn g B2) x    ------the way sets that invFun g is totally wrong

  have h0 : BijOn (invFunOn g B2) A2 B2 := BijOn_invFun h2

  have p1: Injective h:= by
    have h1_1 : ∀ x_1 x_2 : α , h (x_1) = h (x_2) → x_1 =x_2:= by
      intro x_1 x_2 h1_1_1
      simp only [h] at h1_1_1
      by_cases hA: x_1 ∈ A1 ∨ x_2 ∈ A1
      · wlog hx : x_1 ∈ A1 generalizing x_1 x_2 h1_1_1 hA ---???????????????
        · symm         --howwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww
          apply this
          apply h1_1_1.symm
          apply hA.symm
          rcases hA with ha1 | ha2
          contradiction
          assumption
        by_cases h22: x_2 ∈ A1
        · rw[if_pos hx,if_pos h22] at h1_1_1
          apply h1.2.1 hx h22 h1_1_1
        · rw [if_neg h22, if_pos hx] at h1_1_1
          -- x₂ ∉ A1, so x₂ ∈ A2
          have hx2A2 : x_2 ∈ A2 := by
            have : x_2 ∈ A1 ∪ A2 := by
              rw [h3.1]
              exact mem_univ x_2
            rcases this with _ | _
            · contradiction
            · assumption
          -- invFunOn g B2 x₂ ∈ A2 and g (invFunOn g B2 x₂) = x₂
          have hxx: invFunOn g B2 x_2 ∈ B2:= by
            have hxxx: ∀ x ∈ A2, invFunOn g B2 x ∈ B2 := by
              exact h0.1
            apply hxxx at hx2A2
            assumption
          rw[← h1_1_1] at hxx
          have this1: f x_1 ∈ B1:= by
            exact h1.1 hx
          have : f x_1 ∈ B1 ∩ B2:= ⟨this1,hxx⟩
          rw[h4.2] at this
          contradiction

      · push_neg at hA
        obtain ⟨ hA1,hA2⟩ := hA
        rw [if_neg hA1,if_neg hA2] at h1_1_1
        have : x_1 ∈ A2 ∧ x_2 ∈ A2 := by
          constructor
          · have hA3 : x_1 ∈ univ := by
              exact mem_univ x_1
            rw[← h3.1] at hA3
            rcases hA3 with hl | hr
            contradiction
            assumption
          · have hA3 : x_2 ∈ univ := by
              exact mem_univ x_2
            rw[← h3.1] at hA3
            rcases hA3 with hl | hr
            contradiction
            assumption
        apply h0.2.1 this.1 this.2 h1_1_1
    exact h1_1
  have p2 : Surjective h := by
    have p2_1: ∀ y , ∃ x , h x = y := by
      intro y
      by_cases hy : y ∈ B1
      · obtain ⟨x, hxA1, hfx⟩ := h1.surjOn hy -------------?????????
        use x
        simp only [h]
        rw [if_pos hxA1, hfx]
      · have hyB2 : y ∈ B2 := by
          have : y ∈ univ := mem_univ y
          rw[← h4.1] at this
          rcases this with thisl | thisl
          contradiction
          assumption
        obtain ⟨x, hxA1, hfx⟩ := h0.surjOn hyB2
        use x
        simp only [h]
        have :x ∉ A1 := by
          have : x∈ univ := mem_univ x
          rw[← h3.1] at this
          rcases this with thisl | thisr
          · intro hx
            have : x ∈ A1 ∩ A2 := ⟨ thisl,hxA1⟩
            rw[h3.2] at this
            exact this
          · by_contra t
            have : x ∈ A1 ∩ A2 := ⟨ t,thisr⟩
            rw[h3.2] at this
            exact this
        rw[if_neg this]
        assumption
    exact p2_1
  use h
  exact ⟨ p1 ,p2⟩

   ----why cant do exact h_disj thisl hxA1, so stupid with h_disj

example {α : Type} (x : α) (h0 : x ∈ (∅ : Set α)) : False := by
  assumption




--------------------theorem for two bijections on disjoint sets----------------------------------------

--------------------------what am i doing -------------------------------------------
#check BijOn

#print invFunOn_eq
#print Set.disjoint_iff
#print Disjoint
#print BijOn_invFun



#print Surjective
#print SurjOn
#print InjOn
#print MapsTo
#print invFunOn------------!!!!

------------------------what am i doing ------------------------------------------


----------------------build injection and surjection-----------------------------------------

theorem fun_union_iff (f : α → β): f '' (⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp only [mem_iUnion,mem_image]
  constructor
  · intro h
    obtain ⟨ x, ⟨i, hxi⟩ ,hy⟩ :=h
    use i
    use x
  · intro h
    obtain ⟨i, x, hx, hy⟩ := h
    use x
    constructor
    · use i
    · exact hy


theorem f_bijon_on_A1 (hf: Injective f): BijOn f (sbSet f g) (f '' (sbSet f g)) := by
  set A1 := sbSet f g with A_def
  set B1 := f '' A1 with B_def
  have h1: InjOn f A1:= by
    exact hf.injOn
  have h2: f '' A1 = B1 := by
    simp only [A_def, B_def, fun_union_iff]
                    --- difficulty: not familiar with SurjOn equivalent def and how to unfold it
  have h3 : SurjOn f A1 B1 := by         -- pretty uncomfortable
    have h3_1: B1 ⊆ f '' A1 := by
      rw[h2]
    exact h3_1
  have h_maps : MapsTo f A1 B1 := by
    have : ∀ x ∈ A1, f x ∈ B1 := by
      intro x hx
      have : f x ∈ f '' A1 := by
        use x
      rw[h2] at this
      exact this
    exact this
  have : BijOn f A1 B1 := ⟨h_maps, h1, h3⟩
  assumption

#print MapsTo

theorem dididiff_iff (C D E : Set α ): D ⊆ E → (C \ D ) \( E \ D )= C \ E := by
  intro h
  calc
    (C \ D) \ (E \ D)
        = C \ (D ∪ (E \ D))   := by rw [diff_diff]
    _   = C \ E              := by
      have : D ∪ (E \ D) = E := by
        simp
        assumption
      rw[this]


theorem g_bijon_on_B2 (hg: Injective g): BijOn g (univ \ f '' (sbSet f g)) (univ \ sbSet f g) := by
  set A2 := univ \ sbSet f g with C_def
  set B2 := univ \ f '' (sbSet f g) with D_def
  have h1: g '' B2 = g '' (univ) \ (g '' (f '' (sbSet f g))) := by
    rw [D_def, image_diff]
    assumption
  have h2 : g '' (f '' (sbSet f g)) = sbSet f g \ sbAux f g 0:=by  -------------------------------------
    rw[sbSet]
    simp only [fun_union_iff]
    have h3 : (⋃ i, g '' (f '' sbAux f g i)) = ⋃ i, sbAux f g (i+1) := by
      simp [sbAux]
    have h4 : ⋃ i, sbAux f g (i+1) = sbSet f g \ sbAux f g 0 := by
        ext x
        constructor
        · intro hx
          simp only [mem_iUnion] at hx
          rw[mem_diff ]
          constructor
          · obtain ⟨i, hx⟩ := hx
            rw[sbSet,mem_iUnion]
            use i + 1
          · obtain ⟨ i ,hx ⟩ := hx
            have t1: i + 1 > 0 := by
              exact Nat.succ_pos i
            have t1: ∃ n ,sbAux f g (i + 1) = g '' (f '' sbAux f g n) := by
               use i
               rfl
            obtain ⟨n, t1⟩ := t1
            by_contra hxa
            rw[t1] at hx
            have : x ∈ g '' (univ) := by
              have : g '' (f '' sbAux f g n) ⊆ g '' (univ) := by
                simp
              apply this at hx
              assumption
            have : x ∉ g '' (univ) := by
              rw[sbAux,mem_diff] at hxa
              exact hxa.2
            contradiction
        · intro hx
          simp only [mem_diff, mem_iUnion] at hx
          obtain ⟨hl, hr⟩ := hx
          rw[sbSet,mem_iUnion] at hl
          obtain ⟨i, hl⟩ := hl
          have : i > 0:= by
            by_contra h
            push_neg at h
            have : i = 0 := by
              exact Nat.eq_zero_of_le_zero h
            rw[this] at hl
            contradiction
          rw[mem_iUnion]
          use i - 1
          have : i - 1 + 1 = i := by
            exact Nat.succ_pred_eq_of_pos this
          rw[this]
          assumption
    rw[h3,h4];rfl  --------------------------------------------------------------------------
  rw[h2] at h1
  have : g '' univ = univ \ sbAux f g 0:= by
    simp [sbAux]
  rw[this] at h1
  have h3: sbAux f g 0 ⊆ sbSet f g := by
    simp [sbSet]
    intro x h
    rw[mem_iUnion]
    use 0
  rw[dididiff_iff (univ) (sbAux f g 0) (sbSet f g)] at h1
  rw[← C_def] at h1        ----finally get g''B2 = A2, then do the same thing as in last theorem
  have h4 : InjOn g B2 := by exact hg.injOn
  have h5 : SurjOn g B2 A2:= by
    have : A2 ⊆ g '' B2 := by
      rw[h1]
    exact this
  have h6: MapsTo g B2 A2 := by
    have : ∀ y ∈ B2, g y ∈ A2:= by
      intro y h
      have : g y ∈ g '' B2:= by
        use y
      rwa [h1] at this ;
    exact this
  exact ⟨ h6 ,h4 ,h5⟩
  assumption

--------------------------build injection and surjection-------------------------------------------------------



-------------------------never mind --------------------------------------------------------------------



theorem schroeder_bernstein [Nonempty β] {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h := by
    set A1 := sbSet f g with A_def
    set B1 := f '' A1 with B_def
    set A2 := univ \ A1 with C_def
    set B2 := univ \ B1 with D_def
    have h1 : A1 ∪ A2 = univ := by
      rw [A_def, C_def, Set.union_diff_self]
      simp
    have h1_1: A1 ∩ A2 = ∅ := by
      rw [A_def, C_def]
      exact Set.inter_diff_self _ _
    have h2 : B1 ∪ B2 = univ := by
      rw [B_def, D_def, Set.union_diff_self]
      simp
    have h2_2 : B1 ∩ B2 = ∅ := by
      rw [ B_def,D_def]
      exact Set.inter_diff_self _ _   ------!!!!!simp not gonna work here
    exact bijective_disjoint (f_bijon_on_A1 f g hf) (g_bijon_on_B2 f g hg) ⟨h1, h1_1⟩  ⟨ h2, h2_2⟩


/- advantages: 1. once the proof get down and approved in lean, the accuracy get guaranteed
   spare the time to examine a lang proof
   2. pretty fast to deal with logic problem and some trivial problem with the help of "simp"
   3. available for a good structure of proof
   4. very convenient to have current goal rendering all the time on the right side



  disadvantages : 1. the cost to learn different lemmas, high demand of using lemma
        2. not as readable as proof in paper, some proof would be less efficient due to the low knowlegement
        3. some "obvious" parts have to be unfolded in the proof
        4. some important lemmas dont exist in the library, for example?? like my fun_union_iff
        5. too many" have " maybe solved by cal


------simp
      write the paper proof
      pick out the lemmas in B-S-theorem
      train to define different things
      pick the exercise presented,talking about the idea.
      central idea for set (turns into logic) and function proving (exists quantifier)
      definitions that in lean 4, and why define like that. also by reading textbook
      family of sets
      40 mins for this last theorem.
      do we register for seminar
      subtle part
      left_right_inverse
      play around with BijOn and image SurjOn stuffs comfortably


-/

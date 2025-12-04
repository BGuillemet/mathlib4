/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage
/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

@[expose] public section

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

/--
The equivalence between natural transformations from the yoneda embedding (to the sheaf category)
and elements of `F.val.obj X`.
-/
def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

theorem yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) :
    yonedaEquiv J f = f.val.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.val.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (J.yonedaEquiv.symm x).val.app Y f = F.val.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g ≫ f) := by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

/--
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g.unop ≫ f) :=
  J.yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) :
    J.yonedaEquiv (α ≫ β) = β.val.app _ (J.yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
    (x : F.val.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEquiv.symm
      ((F.val.map f.op) x) := by
  apply J.yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply]
  rw [yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
    (x : F.val.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = f.val.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/--
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = f.val.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.val.obj X) :
    J.yonedaEquiv.symm (F.val.map f t) = J.yoneda.map f.unop ≫ J.yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/--
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions with morphisms
`yoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

/-- The curried version of the Yoneda lemma for sheaves. -/
def largeCurriedYonedaLemma :
    J.yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}
      ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

@[simp]
lemma largeCurriedYonedaLemma_app_app (X : C) (F : Sheaf J (Type v)) :
    (J.largeCurriedYonedaLemma.app (op X)).app F
    = (J.yonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

/-- A version of `yonedaEquiv` for `uliftYoneda`. -/
def uliftYonedaEquiv {X : C} {F : Sheaf J (Type (max v v'))} :
    ((uliftYoneda.{v'} J).obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv := uliftYonedaEquiv

theorem uliftYonedaEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) : uliftYonedaEquiv.{v'} J f = f.val.app (op X) ⟨𝟙 X⟩ :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_apply := uliftYonedaEquiv_apply

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_apply := uliftYonedaEquiv_apply

@[simp]
theorem uliftYonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (x : F.val.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    (J.uliftYonedaEquiv.symm x).val.app Y ⟨f⟩ = F.val.map f.op x :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_app_apply :=
  uliftYonedaEquiv_symm_app_apply

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_app_apply :=
  uliftYonedaEquiv_symm_app_apply

/-- See also `uliftYonedaEquiv_naturality'` for a more general version. -/
lemma uliftYonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
      F.val.map g.op (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g ≫ f) := by
  change (f.val.app (op X) ≫ F.val.map g.op) ⟨𝟙 X⟩ = f.val.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.val.naturality]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality :=
  uliftYonedaEquiv_naturality

/-- Variant of `uliftYonedaEquiv_naturality` with general `g`. This is technically strictly more
general than `uliftYonedaEquiv_naturality`, but `uliftYonedaEquiv_naturality` is sometimes
preferable because it can avoid the "motive is not type correct" error. -/
lemma uliftYonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.val.map g (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g.unop ≫ f) :=
  J.uliftYonedaEquiv_naturality _ _

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_naturality' :=
  uliftYonedaEquiv_naturality'

lemma uliftYonedaEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
    (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.val.app _ (J.uliftYonedaEquiv α) :=
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_comp := uliftYonedaEquiv_comp

lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    (uliftYonedaEquiv.{v'} J) (J.uliftYoneda.map f) = ⟨f⟩ := by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_yonedaULift_map :=
  uliftYonedaEquiv_uliftYoneda_map

lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
    (x : F.val.obj ⟨X⟩) :
    J.uliftYoneda.map f ≫ J.uliftYonedaEquiv.symm x =
      J.uliftYonedaEquiv.symm ((F.val.map f.op) x) := by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_left :=
  uliftYonedaEquiv_symm_naturality_left

lemma uliftYonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max v v'))}
    (f : F ⟶ F') (x : F.val.obj ⟨X⟩) :
    J.uliftYonedaEquiv.symm x ≫ f = J.uliftYonedaEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_naturality_right :=
  uliftYonedaEquiv_symm_naturality_right

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_uliftYonedaEquiv {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.val.map g.op (J.uliftYonedaEquiv f) = f.val.app (op Y) ⟨g⟩ := by
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv := map_uliftYonedaEquiv

/-- Variant of `map_uliftYonedaEquiv` with general `g`. This is technically strictly more general
than `map_uliftYonedaEquiv`, but `map_uliftYonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error. -/
lemma map_uliftYonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.val.map g (J.uliftYonedaEquiv f) = f.val.app Y ⟨g.unop⟩ := by
  rw [uliftYonedaEquiv_naturality', uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]

@[deprecated (since := "2025-11-10")] alias map_yonedaULiftEquiv' := map_uliftYonedaEquiv'

lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
    (t : F.val.obj X) : J.uliftYonedaEquiv.symm (F.val.map f t) =
      J.uliftYoneda.map f.unop ≫ J.uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

@[deprecated (since := "2025-11-10")] alias yonedaULiftEquiv_symm_map := uliftYonedaEquiv_symm_map

/-- Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree. -/
lemma hom_ext_uliftYoneda {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

@[deprecated (since := "2025-11-10")] alias hom_ext_yonedaULift := hom_ext_uliftYoneda

/-- A variant of the curried version of the Yoneda lemma with a raise in the universe level. -/
def largeCurriedUliftYonedaLemma :
    J.uliftYoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type max v v') ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u}
      ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaOpCompCoyoneda
    ((whiskeringLeft _ _ _).obj _))

@[simp]
lemma largeCurriedUliftYonedaLemma_app_app (X : C) (F : Sheaf J (Type (max v v'))) :
    (J.largeCurriedUliftYonedaLemma.app (op X)).app F
    = (J.uliftYonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

abbrev familyOfElementsPtVal {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ J.yoneda)) :
    S.arrows.FamilyOfElements s.pt.val :=
  (fun _ f hf => J.yonedaEquiv (s.ι.app ⟨Over.mk f, hf⟩))

theorem familyOfElementsPtVal_compatible {X : C} {S : Sieve X}
    (s : Limits.Cocone (S.arrows.diagram ⋙ J.yoneda)) :
    (J.familyOfElementsPtVal s).Compatible := by
  refine (Presieve.compatible_iff_sieveCompatible _).2 (fun Y Z f g hf => ?_)
  rw [yonedaEquiv_naturality]
  let : ({ obj := Over.mk (g ≫ f), property := S.downward_closed hf g } : S.arrows.category)
      ⟶ { obj := Over.mk f, property := hf} :=
    Over.homMk g
  simp only [id_obj, ← s.w this, comp_obj, ObjectProperty.ι_obj, Over.forget_obj,
    Over.mk_left, const_obj_obj, Functor.comp_map, ObjectProperty.ι_map, Over.forget_map,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

@[simps]
def compatibleYonedaFamily_toCocone (F : Sheaf J (Type v)) {X : C} (R : Presieve X)
    (x : Presieve.FamilyOfElements F.val R) (hx : x.Compatible) :
    Limits.Cocone (R.diagram ⋙ J.yoneda) where
  pt := F
  ι := {
    app := fun ⟨f, hf⟩ => J.yonedaEquiv.invFun (x f.hom hf)
    naturality := fun ⟨f, hf⟩ ⟨g, hg⟩ φ => by
      simp [J.yonedaEquiv_symm_naturality_left, hx φ.left (𝟙 _) hg hf]
    }

theorem isSheaf_sup (K L : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type max u v) :
    Presieve.IsSheaf (K ⊔ L) P ↔ Presieve.IsSheaf K P ∧ Presieve.IsSheaf L P := by
  rw [← (Coverage.gi C).l_u_eq K, ← (Coverage.gi C).l_u_eq L, ← (Coverage.gi C).gc.l_sup,
    Presieve.isSheaf_sup, (Coverage.gi C).l_u_eq K, (Coverage.gi C).l_u_eq L]

omit [J.Subcanonical] in
theorem mem_of_isSheafFor_pullback (X : C) (S : Sieve X)
    (hS : ∀ (F : Sheaf J (Type max u v)) {Y : C} {f : Y ⟶ X},
      Presieve.IsSheafFor F.val (S.pullback f).arrows) :
    S ∈ J X := by
  let J₂ := J ⊔ (S.arrows.skyscraperPrecoverage.toGrothendieck')
  have : J = J₂ := by
    refine topology_eq_iff_same_sheaves.2 (fun P => ?_)
    constructor <;> intro hP
    · unfold J₂
      refine (isSheaf_sup _ _ _).2 ⟨hP, ?_⟩
      rw [S.arrows.skyscraperPrecoverage.isSheaf_toGrothendieck'_iff]
      intro Y Z f R hR
      cases hR
      rw [Sieve.generate_sieve]
      exact hS ⟨P, (isSheaf_iff_isSheaf_of_type J P).2 hP⟩
    · exact Presieve.isSheaf_of_le P le_sup_left hP
  rw [this]
  apply le_sup_right (a := J)
  rw [← S.generate_sieve]
  apply Precoverage.generate_mem_toGrothendieck'
  simp

/-- A sieve of `X` belongs to a subcanonical topology `J` if and only if `yoneda X` is a colimit
  of the diagram associated to `S` composed with the Yoneda embedding into `Sheaf J (Type v)`. -/
theorem covering_iff_colimit_yoneda {X : C} (S : Sieve X) :
    S ∈ J X ↔ Nonempty (Limits.IsColimit (J.yoneda.mapCocone S.arrows.cocone)) := by
  constructor
  · exact fun hS => Nonempty.intro {
      desc s := J.yonedaEquiv.invFun ((s.pt.cond.isSheafFor S hS).amalgamate
        (J.familyOfElementsPtVal s) (J.familyOfElementsPtVal_compatible s))
      fac s j := by
        simp only [id_obj, comp_obj, ObjectProperty.ι_obj, Over.forget_obj, mapCocone_pt,
          Limits.Cocone.whisker_pt, Over.forgetCocone_pt, const_obj_obj, mapCocone_ι_app,
          Limits.Cocone.whisker_ι, whiskerLeft_app, Over.forgetCocone_ι_app, Equiv.invFun_as_coe,
          yonedaEquiv_symm_naturality_left, Presieve.IsSheafFor.valid_glue _ _ _ j.property,
          familyOfElementsPtVal, J.yonedaEquiv.symm_apply_apply]
        rfl
      uniq s m hm := by
        have h := (s.pt.cond.isSheafFor S hS) (J.familyOfElementsPtVal s)
          (J.familyOfElementsPtVal_compatible s)
        refine J.yonedaEquiv.eq_symm_apply.2 (h.unique ?_ ?_)
        · intro _ _ _
          rw [familyOfElementsPtVal, J.yonedaEquiv_naturality m, ← hm]
          rfl
        · exact (s.pt.cond.isSheafFor S hS).isAmalgamation (familyOfElementsPtVal_compatible J s)
      }
  · refine fun ⟨h⟩ => ?_
    have (F : Sheaf J (Type v)) : Presieve.IsSheafFor F.val S.arrows := by
      refine fun x hx => ?_
      use J.yonedaEquiv (h.desc (J.compatibleYonedaFamily_toCocone _ _ x hx))
      constructor
      · intro _ f hf
        rw [J.yonedaEquiv_naturality]
        have : J.yoneda.map f = (J.yoneda.mapCocone S.arrows.cocone).ι.app ⟨Over.mk f, hf⟩ :=
          rfl
        rw [this, h.fac]
        simp
      · intro a ha
        rw [← h.uniq _ (J.yonedaEquiv.invFun a)
          fun ⟨_, hf⟩ => by simp [yonedaEquiv_symm_naturality_left, ha _ hf]]
        exact J.yonedaEquiv.symm_apply_eq.1 rfl
    sorry

theorem fnejzi (F : Sheaf (Sheaf.canonicalTopology C) (Type max u v)) : IsRepresentable F.val := by
    #check natIsoColimitOverYoneda'.{u, v, max u v} F.val
    sorry

end CategoryTheory.GrothendieckTopology

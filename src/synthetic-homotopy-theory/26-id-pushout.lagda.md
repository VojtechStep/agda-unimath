# Formalization of the Symmetry book - 26 id pushout

```agda
{-# OPTIONS --lossy-unification #-}
module synthetic-homotopy-theory.26-id-pushout where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.sections
open import foundation.span-diagrams
open import foundation.transposition-identifications-along-equivalences
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.descent-data-pushouts-equivalence-families
open import synthetic-homotopy-theory.descent-data-pushouts-identity-types
open import synthetic-homotopy-theory.descent-property-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.morphisms-descent-data-pushouts
open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The universal property of identity types of pushouts states that given an
element `a₀ : A`, the descent data for `Id (inl a₀) : X → 𝒰` equipped with
`refl : inl a₀ ＝ inl a₀` is the initial pointed descent data.

This is analogous to the universal property of contractible types with respect
to pointed types and maps. To avoid having to build the infrastructure of
pointed descent data, we actually formalize the universal property as the
universal property of contractible types, i.e. that the evaluation map at
`p : PA a₀` taking a morphism `h : (PA, PB, PS) → (QA, QB, QS)` to
`hA a₀ p : QA a₀` is an equivalence.

The evaluation map being an equivalence

- DD has induction -> family has induction
- family has induction -> family has universal property
- family has universal property -> it is equivalent to Id
- family is equivalent to Id -> DD is equivalent to Id DD

```agda
open import foundation.torsorial-type-families
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a₀ : A} (b₀ : B a₀)
  (is-contr-AB : is-torsorial B)
  where

  open import foundation.contractible-maps
  open import foundation.equality-dependent-pair-types
  open import foundation.equivalence-extensionality
  open import foundation.fibers-of-maps
  open import foundation.functoriality-dependent-function-types
  open import foundation.functoriality-dependent-pair-types
  open import foundation.function-extensionality
  open import foundation.homotopies
  open import foundation.type-arithmetic-dependent-pair-types

  map-asdasd :
    ((a : A) → (a₀ ＝ a) → B a) → ((a : A) → (a₀ ＝ a) ≃ B a)
  map-asdasd h a =
    (h a) ,
    fundamental-theorem-id is-contr-AB h a

  is-equiv-map-asdasd : is-equiv map-asdasd
  is-equiv-map-asdasd =
    is-equiv-is-invertible
      ( λ e a → map-equiv (e a))
      ( λ e → eq-htpy (λ a → eq-htpy-equiv refl-htpy))
      ( refl-htpy)

  asdasd :
    ((a : A) → (a₀ ＝ a) → B a) ≃ ((a : A) → (a₀ ＝ a) ≃ B a)
  pr1 asdasd = map-asdasd
  pr2 asdasd = is-equiv-map-asdasd

  abstract
    fundamental-theorem-id-ext :
      is-contr
        ( Σ ( (a : A) → (a₀ ＝ a) ≃ B a)
            ( λ e → map-equiv (e a₀) refl ＝ b₀))
    fundamental-theorem-id-ext =
      is-contr-equiv'
        ( fiber (ev-refl a₀ {B = λ a _ → B a}) b₀)
        ( equiv-Σ-equiv-base _ asdasd)
        ( is-contr-map-is-equiv
          ( is-equiv-ev-refl a₀)
          ( b₀))
```

```agda
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4) {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-descent-data-pushout P a₀)
  where

  ev-refl-section-descent-data-pushout :
    {l5 : Level}
    (Q :
      descent-data-pushout (span-diagram-flattening-descent-data-pushout P) l5)
    (t : section-descent-data-pushout Q) →
    left-family-descent-data-pushout Q (a₀ , p₀)
  ev-refl-section-descent-data-pushout Q t = pr1 t (a₀ , p₀)

  induction-principle-identity-system-descent-data-pushout : UUω
  induction-principle-identity-system-descent-data-pushout =
    {l5 : Level}
    (Q :
      descent-data-pushout
        ( span-diagram-flattening-descent-data-pushout P)
        ( l5)) →
    section (ev-refl-section-descent-data-pushout Q)

module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  (P : descent-data-pushout 𝒮 l4) {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-descent-data-pushout P a₀)
  where

  ev-point-hom-descent-data-pushout :
    {l5 : Level} (Q : descent-data-pushout 𝒮 l5) →
    (h : hom-descent-data-pushout P Q) →
    left-family-descent-data-pushout Q a₀
  ev-point-hom-descent-data-pushout Q h =
    left-map-hom-descent-data-pushout P Q h a₀ p₀

  universal-property-identity-system-descent-data-pushout : UUω
  universal-property-identity-system-descent-data-pushout =
    {l5 : Level} (Q : descent-data-pushout 𝒮 l5) →
    is-equiv (ev-point-hom-descent-data-pushout Q)

module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (a₀ : domain-span-diagram 𝒮)
  where

  square-induction-principle-descent-data-pushout-identity-type :
    {l5 : Level}
    (Q :
      descent-data-pushout
        ( span-diagram-flattening-descent-data-pushout
          ( descent-data-pushout-identity-type c (horizontal-map-cocone _ _ c a₀)))
        ( l5)) →
    let
      fam-Q =
        family-with-descent-data-pushout-descent-data-pushout
          ( flattening-lemma-descent-data-pushout _ _ c
            ( descent-data-pushout-identity-type c (horizontal-map-cocone _ _ c a₀))
            ( λ x → horizontal-map-cocone _ _ c a₀ ＝ x)
            ( inv-equiv-descent-data-pushout _ _
              ( equiv-descent-data-pushout-identity-type c (horizontal-map-cocone _ _ c a₀)))
            ( dependent-universal-property-universal-property-pushout _ _ _ up-c))
          ( Q)
    in
    coherence-square-maps
      ( section-descent-data-section-family-cocone-span-diagram fam-Q)
      ( ev-refl (horizontal-map-cocone _ _ c a₀) ∘ ev-pair)
      ( ev-refl-section-descent-data-pushout
        ( descent-data-pushout-identity-type c (horizontal-map-cocone _ _ c a₀))
        ( refl)
        ( Q))
      ( left-map-family-with-descent-data-pushout fam-Q (a₀ , refl))
  square-induction-principle-descent-data-pushout-identity-type Q t = refl

  induction-principle-descent-data-pushout-identity-type :
    induction-principle-identity-system-descent-data-pushout
      ( descent-data-pushout-identity-type c (horizontal-map-cocone _ _ c a₀))
      ( refl)
  induction-principle-descent-data-pushout-identity-type Q =
    section-right-map-triangle _ _ _
      ( square-induction-principle-descent-data-pushout-identity-type Q)
      ( section-comp _ _
        ( section-comp _ _
          ( section-is-equiv is-equiv-ev-pair)
          ( section-is-equiv (is-equiv-ev-refl _)))
        ( section-map-equiv
          ( compute-left-family-cocone-descent-data-pushout
            ( flattening-lemma-descent-data-pushout _ _ c
              ( descent-data-pushout-identity-type c
                ( horizontal-map-cocone _ _ c a₀))
              ( λ x → horizontal-map-cocone _ _ c a₀ ＝ x)
              ( inv-equiv-descent-data-pushout _ _
                ( equiv-descent-data-pushout-identity-type c
                  ( horizontal-map-cocone _ _ c a₀)))
              ( dependent-universal-property-universal-property-pushout _ _ _
                ( up-c)))
            ( Q)
            ( a₀ , refl))))

module _
  {l1 l2 l3 l4 l5 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : descent-data-pushout 𝒮 l5) {a₀ : domain-span-diagram 𝒮}
  (p₀ : left-family-descent-data-pushout P a₀)
  where

  map-family-identity-type-induction-principle-identity-system-descent-data-pushout :
    (x : X) → (horizontal-map-cocone _ _ c a₀ ＝ x) →
    family-cocone-descent-data-pushout up-c P x
  map-family-identity-type-induction-principle-identity-system-descent-data-pushout
    .(horizontal-map-cocone _ _ c a₀) refl =
    map-compute-inv-left-family-cocone-descent-data-pushout up-c P a₀ p₀

  square-foo :
    {l5 : Level}
    (Q :
      descent-data-pushout
        ( span-diagram-flattening-descent-data-pushout P)
        ( l5)) →
    let
      fam-Q =
        family-with-descent-data-pushout-descent-data-pushout
          ( flattening-lemma-descent-data-pushout _ _ c P
            ( family-cocone-descent-data-pushout up-c P)
            ( inv-equiv-family-cocone-descent-data-pushout up-c P)
            ( dependent-universal-property-universal-property-pushout _ _ _ up-c))
          ( Q)
    in
    coherence-square-maps
      ( section-descent-data-section-family-cocone-span-diagram fam-Q)
      ( ( ev-refl-identity-system
          ( map-compute-inv-left-family-cocone-descent-data-pushout up-c P a₀
            ( p₀))
          { P =
            ev-pair (family-cocone-family-with-descent-data-pushout fam-Q)}) ∘
        ( ev-pair))
      ( ev-refl-section-descent-data-pushout P p₀ Q)
      ( left-map-family-with-descent-data-pushout fam-Q (a₀ , p₀))
  square-foo Q t = refl

  square-foo' :
    {l5 : Level}
    (Q : (x : X) → family-cocone-descent-data-pushout up-c P x → UU l5) →
    let
      fam-Q =
        family-with-descent-data-pushout-family-cocone
          ( cocone-flattening-descent-data-pushout _ _ c
            ( P)
            ( family-cocone-descent-data-pushout up-c P)
            ( inv-equiv-family-cocone-descent-data-pushout up-c P))
          ( ind-Σ Q)
    in
    coherence-square-maps
      ( section-descent-data-section-family-cocone-span-diagram fam-Q ∘ ind-Σ)
      ( ev-refl-identity-system
        ( map-compute-inv-left-family-cocone-descent-data-pushout up-c P a₀ p₀))
      ( ev-refl-section-descent-data-pushout P p₀
        ( descent-data-family-with-descent-data-pushout fam-Q))
      ( left-map-family-with-descent-data-pushout fam-Q (a₀ , p₀))
  square-foo' Q t = refl

  is-equiv-map-family-identity-type-induction-principle-identity-system-descent-data-pushout :
    induction-principle-identity-system-descent-data-pushout P p₀ →
    (x : X) →
    is-equiv
      ( map-family-identity-type-induction-principle-identity-system-descent-data-pushout
        ( x))
  is-equiv-map-family-identity-type-induction-principle-identity-system-descent-data-pushout
    ip-P =
    fundamental-theorem-id-is-identity-system
      ( horizontal-map-cocone _ _ c a₀)
      ( map-compute-inv-left-family-cocone-descent-data-pushout up-c P a₀ p₀)
      ( λ Q →
        section-left-map-triangle _ _ _
          ( square-foo' Q)
          ( section-comp _ _
            ( section-is-equiv is-equiv-ind-Σ)
            ( section-map-equiv
              ( asdf _
                ( flattening-lemma-descent-data-pushout _ _ c
                  ( P)
                  ( family-cocone-descent-data-pushout up-c P)
                  ( inv-equiv-family-cocone-descent-data-pushout up-c P)
                  ( dependent-universal-property-universal-property-pushout _ _
                    ( _)
                    ( up-c))))))
          ( ip-P _))
      ( map-family-identity-type-induction-principle-identity-system-descent-data-pushout)

  abstract
    equiv-identity-type-induction-principle-identity-system-descent-data-pushout :
      (ip-P : induction-principle-identity-system-descent-data-pushout P p₀) →
      equiv-descent-data-pushout
        ( descent-data-pushout-identity-type c (horizontal-map-cocone _ _ c a₀))
        ( P)
    equiv-identity-type-induction-principle-identity-system-descent-data-pushout
      ip-P =
      map-compute-section-descent-data-pushout-equivalence-family
        ( family-with-descent-data-pushout-identity-type c
          ( horizontal-map-cocone _ _ c a₀))
        ( fam-P)
        ( section-descent-data-section-family-cocone-span-diagram
          ( family-with-descent-data-pushout-equivalence-family _ _)
          ( λ x →
            ( ( map-family-identity-type-induction-principle-identity-system-descent-data-pushout x)) ,
              ( is-equiv-map-family-identity-type-induction-principle-identity-system-descent-data-pushout
                ( ip-P)
                ( x))))
      where
        fam-P : family-with-descent-data-pushout c l5
        fam-P =
          family-with-descent-data-pushout-descent-data-pushout up-c P

    uniqueness-foo :
      (ip-P : induction-principle-identity-system-descent-data-pushout P p₀) →
      is-contr
        ( Σ ( equiv-descent-data-pushout
              ( descent-data-pushout-identity-type c
                ( horizontal-map-cocone _ _ c a₀))
              ( P))
            ( λ e → left-map-equiv-descent-data-pushout _ _ e a₀ refl ＝ p₀))
    uniqueness-foo ip-P =
      is-contr-equiv'
        ( Σ ( (x : X) →
              (horizontal-map-cocone _ _ c a₀ ＝ x) ≃
              family-cocone-family-with-descent-data-pushout fam-P x)
            ( λ e → map-equiv (e (horizontal-map-cocone _ _ c a₀)) refl ＝ p₀'))
        ( equiv-Σ _
          ( ( compute-section-descent-data-pushout-equivalence-family
              ( family-with-descent-data-pushout-identity-type c
                ( horizontal-map-cocone _ _ c a₀))
              ( fam-P)) ∘e
            ( asdf
              ( family-with-descent-data-pushout-equivalence-family _ fam-P)
              ( up-c)))
          ( λ e →
            inv-equiv
              ( eq-transpose-equiv
                ( left-equiv-family-with-descent-data-pushout fam-P a₀)
                ( _)
                ( p₀))))
        ( fundamental-theorem-id-ext p₀'
          ( is-torsorial-is-identity-system
            ( horizontal-map-cocone _ _ c a₀)
            ( p₀')
            ( λ Q →
              section-left-map-triangle _ _ _
                ( square-foo' Q)
                ( section-comp _ _
                  ( section-is-equiv is-equiv-ind-Σ)
                  ( section-map-equiv
                    ( asdf _
                      ( flattening-lemma-descent-data-pushout _ _ c
                        ( P)
                        ( family-cocone-descent-data-pushout up-c P)
                        ( inv-equiv-family-cocone-descent-data-pushout up-c P)
                        ( dependent-universal-property-universal-property-pushout _ _
                          ( _)
                          ( up-c))))))
                ( ip-P _))))
      where
      fam-P : family-with-descent-data-pushout c l5
      fam-P = family-with-descent-data-pushout-descent-data-pushout up-c P
      p₀' :
        family-cocone-family-with-descent-data-pushout
          ( fam-P)
          ( horizontal-map-cocone _ _ c a₀)
      p₀' =
        map-compute-inv-left-family-cocone-descent-data-pushout up-c P a₀ p₀
```

# Functoriality of dependent pair types

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module foundation.functoriality-dependent-pair-types where

open import foundation-core.functoriality-dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
```

</details>

## Properties

### A family of squares over a pullback squares is a family of pullback squares if and only if the induced square of total spaces is a pullback square

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X}
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b))
  (c : cone f g C) (c' : cone-family PX f' g' c PC)
  where

  tot-cone-cone-family :
    cone (map-Σ PX f f') (map-Σ PX g g') (Σ C PC)
  pr1 tot-cone-cone-family =
    map-Σ _ (vertical-map-cone f g c) (λ x → pr1 (c' x))
  pr1 (pr2 tot-cone-cone-family) =
    map-Σ _ (horizontal-map-cone f g c) (λ x → (pr1 (pr2 (c' x))))
  pr2 (pr2 tot-cone-cone-family) =
    htpy-map-Σ PX
      ( coherence-square-cone f g c)
      ( λ z →
        ( f' (vertical-map-cone f g c z)) ∘
        ( vertical-map-cone
          ( ( tr PX (coherence-square-cone f g c z)) ∘
            ( f' (vertical-map-cone f g c z)))
          ( g' (horizontal-map-cone f g c z))
          ( c' z)))
      ( λ z →
        coherence-square-cone
          ( ( tr PX (coherence-square-cone f g c z)) ∘
            ( f' (vertical-map-cone f g c z)))
          ( g' (horizontal-map-cone f g c z))
          ( c' z))

  map-canonical-pullback-tot-cone-cone-fam-right-factor :
    Σ ( canonical-pullback f g)
      ( λ t → canonical-pullback ((tr PX (π₃ t)) ∘ (f' (π₁ t))) (g' (π₂ t))) →
    Σ ( Σ A PA)
      ( λ aa' → Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
        ( λ bα → Σ (PB (pr1 bα))
          ( λ b' → Id
            ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
            ( g' (pr1 bα) b'))))
  map-canonical-pullback-tot-cone-cone-fam-right-factor =
    map-interchange-Σ-Σ
      ( λ a bα a' → Σ (PB (pr1 bα))
        ( λ b' → Id (tr PX (pr2 bα) (f' a a')) (g' (pr1 bα) b')))

  map-canonical-pullback-tot-cone-cone-fam-left-factor :
    (aa' : Σ A PA) →
    Σ (Σ B (λ b → Id (f (pr1 aa')) (g b)))
      ( λ bα → Σ (PB (pr1 bα))
        ( λ b' → Id
          ( tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')))
          ( g' (pr1 bα) b'))) →
    Σ ( Σ B PB)
      ( λ bb' → Σ (Id (f (pr1 aa')) (g (pr1 bb')))
        ( λ α → Id (tr PX α (f' (pr1 aa') (pr2 aa'))) (g' (pr1 bb') (pr2 bb'))))
  map-canonical-pullback-tot-cone-cone-fam-left-factor aa' =
    ( map-interchange-Σ-Σ
      ( λ b α b' → Id (tr PX α (f' (pr1 aa') (pr2 aa'))) (g' b b')))

  map-canonical-pullback-tot-cone-cone-family :
    Σ ( canonical-pullback f g)
      ( λ t → canonical-pullback ((tr PX (π₃ t)) ∘ (f' (π₁ t))) (g' (π₂ t))) →
    canonical-pullback (map-Σ PX f f') (map-Σ PX g g')
  map-canonical-pullback-tot-cone-cone-family =
    ( tot (λ aa' →
      ( tot (λ bb' → eq-pair-Σ')) ∘
      ( map-canonical-pullback-tot-cone-cone-fam-left-factor aa'))) ∘
    ( map-canonical-pullback-tot-cone-cone-fam-right-factor)

  is-equiv-map-canonical-pullback-tot-cone-cone-family :
    is-equiv map-canonical-pullback-tot-cone-cone-family
  is-equiv-map-canonical-pullback-tot-cone-cone-family =
    is-equiv-comp
      ( tot (λ aa' →
        ( tot (λ bb' → eq-pair-Σ')) ∘
        ( map-canonical-pullback-tot-cone-cone-fam-left-factor aa')))
      ( map-canonical-pullback-tot-cone-cone-fam-right-factor)
      ( is-equiv-map-interchange-Σ-Σ
        ( λ a bα a' → Σ (PB (pr1 bα))
          ( λ b' → Id (tr PX (pr2 bα) (f' a a')) (g' (pr1 bα) b'))))
      ( is-equiv-tot-is-fiberwise-equiv (λ aa' → is-equiv-comp
        ( tot (λ bb' → eq-pair-Σ'))
        ( map-canonical-pullback-tot-cone-cone-fam-left-factor aa')
        ( is-equiv-map-interchange-Σ-Σ _)
        ( is-equiv-tot-is-fiberwise-equiv (λ bb' → is-equiv-eq-pair-Σ
          ( pair (f (pr1 aa')) (f' (pr1 aa') (pr2 aa')))
          ( pair (g (pr1 bb')) (g' (pr1 bb') (pr2 bb')))))))

  triangle-canonical-pullback-tot-cone-cone-family :
    ( gap (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family) ~
    ( ( map-canonical-pullback-tot-cone-cone-family) ∘
      ( map-Σ _
        ( gap f g c)
        ( λ x → gap
          ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
          ( g' (pr1 (pr2 c) x))
          ( c' x))))
  triangle-canonical-pullback-tot-cone-cone-family x =
    refl

  is-pullback-family-is-pullback-tot :
    is-pullback f g c →
    is-pullback
      (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family →
    (x : C) →
    is-pullback
      ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
      ( g' (pr1 (pr2 c) x))
      ( c' x)
  is-pullback-family-is-pullback-tot is-pb-c is-pb-tot =
    is-fiberwise-equiv-is-equiv-map-Σ _
      ( gap f g c)
      ( λ x → gap
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x))
      ( is-pb-c)
      ( is-equiv-right-factor-htpy
        ( gap (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family)
        ( map-canonical-pullback-tot-cone-cone-family)
        ( map-Σ _
          ( gap f g c)
          ( λ x → gap
            ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
            ( g' (pr1 (pr2 c) x))
            ( c' x)))
        ( triangle-canonical-pullback-tot-cone-cone-family)
        ( is-equiv-map-canonical-pullback-tot-cone-cone-family)
        ( is-pb-tot))

  is-pullback-tot-is-pullback-family :
    is-pullback f g c →
    ( (x : C) →
      is-pullback
        ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
        ( g' (pr1 (pr2 c) x))
        ( c' x)) →
    is-pullback
      (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family
  is-pullback-tot-is-pullback-family is-pb-c is-pb-c' =
    is-equiv-comp-htpy
      ( gap (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family)
      ( map-canonical-pullback-tot-cone-cone-family)
      ( map-Σ _
        ( gap f g c)
        ( λ x → gap
          ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
          ( g' (pr1 (pr2 c) x))
          ( c' x)))
      ( triangle-canonical-pullback-tot-cone-cone-family)
      ( is-equiv-map-Σ _
        ( gap f g c)
        ( λ x → gap
          ( (tr PX (pr2 (pr2 c) x)) ∘ (f' (pr1 c x)))
          ( g' (pr1 (pr2 c) x))
          ( c' x))
          ( is-pb-c)
          ( is-pb-c'))
      ( is-equiv-map-canonical-pullback-tot-cone-cone-family)
```

### Commuting squares of maps on total spaces

#### Functoriality of `Σ` preserves commuting squares of maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {P : A → UU l2}
  {B : UU l3} {Q : B → UU l4}
  {C : UU l5} {R : C → UU l6}
  {D : UU l7} (S : D → UU l8)
  {top' : A → C} {left' : A → B} {right' : C → D} {bottom' : B → D}
  (top : (a : A) → P a → R (top' a))
  (left : (a : A) → P a → Q (left' a))
  (right : (c : C) → R c → S (right' c))
  (bottom : (b : B) → Q b → S (bottom' b))
  where

  coherence-square-maps-Σ :
    {H' : coherence-square-maps top' left' right' bottom'} →
    ( (a : A) (p : P a) →
      dependent-identification S
        ( H' a)
        ( bottom _ (left _ p))
        ( right _ (top _ p))) →
    coherence-square-maps
      ( map-Σ R top' top)
      ( map-Σ Q left' left)
      ( map-Σ S right' right)
      ( map-Σ S bottom' bottom)
  coherence-square-maps-Σ {H'} H (a , p) = eq-pair-Σ (H' a) (H a p)
```

#### Commuting squares of induced maps on total spaces

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {P : A → UU l2} {Q : A → UU l3} {R : A → UU l4} {S : A → UU l5}
  (top : (a : A) → P a → R a)
  (left : (a : A) → P a → Q a)
  (right : (a : A) → R a → S a)
  (bottom : (a : A) → Q a → S a)
  where

  coherence-square-maps-tot :
    ((a : A) → coherence-square-maps (top a) (left a) (right a) (bottom a)) →
    coherence-square-maps (tot top) (tot left) (tot right) (tot bottom)
  coherence-square-maps-tot H (a , p) = eq-pair-Σ refl (H a p)
```

#### `map-Σ-map-base` preserves commuting squares of maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} (S : D → UU l5)
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  where

  coherence-square-maps-map-Σ-map-base :
    (H : coherence-square-maps top left right bottom) →
    coherence-square-maps
      ( map-Σ (S ∘ right) top (λ a → tr S (H a)))
      ( map-Σ-map-base left (S ∘ bottom))
      ( map-Σ-map-base right S)
      ( map-Σ-map-base bottom S)
  coherence-square-maps-map-Σ-map-base H (a , p) = eq-pair-Σ (H a) refl

  coherence-square-maps-map-Σ-map-base' :
    ( H : coherence-square-maps top left right bottom) →
    coherence-square-maps
      ( map-Σ-map-base top (S ∘ right))
      ( map-Σ (S ∘ bottom) left (λ a → tr S (inv (H a))))
      ( map-Σ-map-base right S)
      ( map-Σ-map-base bottom S)
  coherence-square-maps-map-Σ-map-base' H (a , p) =
    -- eq-pair-Σ (H a) (is-retraction-map-equiv (equiv-tr S (H a)) p)
    eq-pair-Σ (H a) (is-section-map-inv-equiv (equiv-tr S (H a)) p)
```

#### Horizontal pasting of commuting squares of total spaces

```text

Σ A A' -----> Σ B B' -----> Σ C C'
  |             |             |
  |             |             |
  v             v             v
Σ X X' -----> Σ Y Y' -----> Σ Z Z'
```

```agda
module _
  { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 : Level}
  { A : UU l1} {A' : A → UU l2}
  { B : UU l3} {B' : B → UU l4}
  { C : UU l5} {C' : C → UU l6}
  { X : UU l7} (X' : X → UU l8)
  { Y : UU l9} {Y' : Y → UU l10}
  { Z : UU l11} {Z' : Z → UU l12}
  { top-left' : A → B} {top-right' : B → C} {left' : A → X} {middle' : B → Y}
  { right' : C → Z} {bottom-left' : X → Y} {bottom-right' : Y → Z}
  ( top-left : (a : A) → A' a → B' (top-left' a) )
  ( top-right : (b : B) → B' b → C' (top-right' b))
  ( left : (a : A) → A' a → X' (left' a))
  ( middle : (b : B) → B' b → Y' (middle' b))
  ( right : (c : C) → C' c → Z' (right' c))
  ( bottom-left : (x : X) → X' x → Y' (bottom-left' x))
  ( bottom-right : (y : Y) → Y' y → Z' (bottom-right' y))
  where

  _ :
    { H' : coherence-square-maps top-left' left' middle' bottom-left'}
    { K' : coherence-square-maps top-right' middle' right' bottom-right'}
    ( H : (a : A) (a' : A' a) →
      dependent-identification
        ( Y')
        ( H' a)
        ( bottom-left (left' a) (left a a'))
        ( middle (top-left' a) (top-left a a'))) →
    ( K : (b : B) (b' : B' b) →
      dependent-identification
        ( Z')
        ( K' b)
        ( bottom-right (middle' b) (middle b b'))
        ( right (top-right' b) (top-right b b'))) →
    pasting-horizontal-coherence-square-maps
      ( map-Σ B' top-left' top-left)
      ( map-Σ C' top-right' top-right)
      ( map-Σ X' left' left)
      ( map-Σ Y' middle' middle)
      ( map-Σ Z' right' right)
      ( map-Σ Y' bottom-left' bottom-left)
      ( map-Σ Z' bottom-right' bottom-right)
      ( coherence-square-maps-Σ Y' top-left left middle bottom-left H)
      ( coherence-square-maps-Σ Z' top-right middle right bottom-right K) ~
    coherence-square-maps-Σ
      Z'
      (λ a → top-right (top-left' a) ∘ top-left a)
      left
      right
      (λ x → bottom-right (bottom-left' x) ∘ bottom-left x)
      {pasting-horizontal-coherence-square-maps top-left' top-right' left' middle' right' bottom-left' bottom-right' H' K'}
      ( λ a a' →
        tr-concat (ap bottom-right' (H' a)) (K' (top-left' a)) _ ∙
        ap
          ( tr Z' (K' (top-left' a)))
          ( substitution-law-tr Z' bottom-right' (H' a) ∙
            {!H a a'!}) ∙
        K (top-left' a) (top-left a a'))
  _ = {!!}

```

### Computation of left whiskering a homotopy given by `eq-pair-Σ` by `map-Σ`

```agda
module _
  { l1 l2 l3 l4 : Level}
  { A : UU l1} {X : UU l2} {B : A → UU l3} {Y : X → UU l4}
  where

  compute-ap-map-Σ-eq-pair-Σ :
    ( f : A → X) (g : (a : A) → B a → Y (f a)) →
    { a a' : A} (p : a ＝ a') {b : B a} {b' : B a'} →
    ( q : dependent-identification B p b b') →
    ( ap (map-Σ Y f g) (eq-pair-Σ p q)) ＝
    eq-pair-Σ
      ( ap f p)
      ( substitution-law-tr Y f p ∙ (inv (preserves-tr g p b) ∙ ap (g a') q))
  compute-ap-map-Σ-eq-pair-Σ f g refl refl = refl

--   compute-left-whisk-map-Σ-map-base-htpy-eq :
--     ( h : A → X) {f g : W → Σ A (B ∘ h)} (H : f ＝ g) →
--     ( (map-Σ-map-base h B) ·l (htpy-eq H)) ~
--     ( λ w →
--       eq-pair-Σ
--         ( ((h ∘ pr1) ·l htpy-eq H) w)
--         ( tr-subst B (h ∘ pr1) (htpy-eq H w) ∙ apd pr2 (htpy-eq H w)))
--   compute-left-whisk-map-Σ-map-base-htpy-eq h refl = refl-htpy

--   compute-left-whisk-eq-pair-Σ-map-Σ-map-base :
--     (h : A → X) {f g : W → Σ A (B ∘ h)} →
--     ( p : (w : W) → pr1 (f w) ＝ pr1 (g w)) →
--     ( q :
--       ( w : W) →
--       dependent-identification (B ∘ h) (p w) (pr2 (f w)) (pr2 (g w))) →
--     ( (map-Σ-map-base h B) ·l (λ w → eq-pair-Σ (p w) (q w))) ~
--     ( λ w → eq-pair-Σ ((h ·l p) w) (tr-subst B h (p w) ∙ q w))
--   compute-left-whisk-eq-pair-Σ-map-Σ-map-base h {f} p q w =
--     {!compute-left-whisk-map-Σ-map-base-htpy-eq h (eq-htpy ?)!}
--     where
--     [i] = {!(pair-eq-Σ-ap (map-Σ-map-base h B) (eq-pair-Σ (p w) (q w)))!}
--     [ii] = pr1-pair-eq-Σ-ap (map-Σ-map-base h B) (eq-pair-Σ (p w) (q w))
```

## See also

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- The universal property of dependent pair types is treated in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).

- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Functorial properties of dependent product types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).

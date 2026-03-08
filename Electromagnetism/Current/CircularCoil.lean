/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Electromagnetism.Dynamics.IsExtrema
import SpaceAndTime.Space.Norm
import SpaceAndTime.Space.Translations
import SpaceAndTime.Space.ConstantSliceDist
import SpaceAndTime.TimeAndSpace.ConstantTimeDist
/-!
# The electrostatics of a circular coil

## i. Overview

This module sets up the circular-coil current context and reference equations for
the electromagnetic potential and field around a steady current loop.

## ii. Key results

## iii. Table of contents

- A. The current density

## iv. References

- https://ntrs.nasa.gov/api/citations/20140002333/downloads/20140002333.pdf

-/

-- NOTE (`TCGIW`): Following the infinite-wire electrostatics structure,
-- complete the definitions and proofs for a circular coil carrying steady current.

namespace Electromagnetism
namespace DistElectromagneticPotential
open minkowskiMatrix SpaceTime SchwartzMap Lorentz
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one
/-!

## A. The current density

-/
end DistElectromagneticPotential
end Electromagnetism

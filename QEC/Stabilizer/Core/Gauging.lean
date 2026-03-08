/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

! This file was added to formalize the low-overhead fault-tolerant gauging measurement
! procedure introduced in arXiv:2410.02213.

-/
import QEC.Stabilizer.Core.CSSCode

import QEC.Stabilizer.Core.LogicalOperators
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

/-! # Gauging Logical Operators

This module formalizes the mechanism of measuring a logical operator by treating it
as a local symmetry and "gauging" it on an auxiliary graph, as detailed in recent
literature on low-overhead fault-tolerant quantum computation (arXiv:2410.02213).

The method achieves polylogarithmic to linear scaling overhead by deforming the 
stablizer code over an attached generic expander graph and projecting locally using 
Gauss's law operators `A_v` and flux operators `B_p`. 
-/

namespace QEC.Stabilizer

open scoped Classical

variable {n k d : ℕ}

/--
We define an auxiliary Edge space `E` over a generic simple graph `G` whose 
vertices `V` are identified with a subset of the data qubits `Fin n`.
The graph should be connected to define proper gauge cycles.
-/
structure GaugingGraph (n : ℕ) where
  V : Type
  [fintypeV : Fintype V]
  [dec_v : DecidableEq V]
  E : Type
  [fintypeE : Fintype E]
  -- Incidence geometry
  edges_of : V → Finset E
  vertices_of : E → Finset V
  
  -- The vertices of this graph map to the support of the logical operator.
  -- This support can be arbitrary data qubits, and potentially include dummy vertices.
  support_map : V → Fin n

namespace GaugingGraph

variable (G : GaugingGraph n)

/-- 
The Gauss's Law Operator $A_v = X_v \prod_{e \ni v} X_e$.
In the stabilizer formalism, we consider this as a localized $X$-type check.
This operator entangles the data vertex `v` with all incident edges `e`.
-/
def gauss_law_operator (v : G.V) :
  -- We represent the local consistency condition that every edge attached to `v`
  -- indeed lists `v` among its incident vertices.
  Prop :=
  ∀ e, e ∈ G.edges_of v → v ∈ G.vertices_of e


end GaugingGraph

end QEC.Stabilizer

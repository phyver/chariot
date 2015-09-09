(*========================================================================
Copyright Pierre Hyvernat, Universite Savoie Mont Blanc

   Pierre.Hyvernat@univ-usmb.fr

This software is a computer program whose purpose is to implement a
programming language in Miranda style. The main point is to have an
adequacy checker for recursive definitions involving nested least and
greatest fixed points.

This software is governed by the CeCILL-B license under French law and
abiding by the rules of distribution of free software.  You can  use,
modify and/ or redistribute the software under the terms of the CeCILL-B
license as circulated by CEA, CNRS and INRIA at the following URL
"http://www.cecill.info".

As a counterpart to the access to the source code and  rights to copy,
modify and redistribute granted by the license, users are provided only
with a limited warranty  and the software's author,  the holder of the
economic rights,  and the successive licensors  have only  limited
liability.

In this respect, the user's attention is drawn to the risks associated
with loading,  using,  modifying and/or developing or reproducing the
software by the user in light of its specific status of free software,
that may mean  that it is complicated to manipulate,  and  that  also
therefore means  that it is reserved for developers  and  experienced
professionals having in-depth computer knowledge. Users are therefore
encouraged to load and test the software's suitability as regards their
requirements in conditions enabling the security of their systems and/or
data to be ensured and,  more generally, to use and operate it in the
same conditions as regards security.

The fact that you are presently reading this means that you have had
knowledge of the CeCILL-B license and that you accept its terms.
========================================================================*)


open Misc
open Env
open Utils
open State
open Pretty
open Typing
open ComputeCaseStruct

let struct_nb = ref 0

let rec term_to_explore (v:(empty,'p,'t) raw_term) : plain_term frozen_term
  = map_raw_term (fun s -> s.bot) (k()) (k()) v

let add_number (v:plain_term frozen_term) : (int*plain_term) frozen_term
  = map_raw_term (function Frozen v -> incr struct_nb; Frozen(!struct_nb,v)) id id v

let rec unfold (env:environment) (p:int->bool) (v:(int*plain_term) frozen_term)
  : (int*plain_term) frozen_term
  = match v with
        | Angel _ | Daimon _ | Var _ | Proj _ | Const _ -> v
        | App(v1,v2) -> App(unfold env p v1, unfold env p v2)
        | Struct(fields,(),()) -> Struct(List.map (function d,v -> d,unfold env p v) fields,(),())
        | Sp(Frozen(n,v),t) when not (p n) -> incr struct_nb; Sp(Frozen(!struct_nb,v),t)
        | Sp(Frozen(n,v),t) (*when (p n)*) ->
                let v = reduce env v in
                add_number v

let to_unfold v = struct_nb := 0; add_number v

let unfold env p v =
    struct_nb:=0; unfold env p v

let rec unfold_to_depth env v depth
  = if depth = 0
    then v
    else
        let v = unfold_to_depth env v (depth-1) in
        unfold env (k true) v


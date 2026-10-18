/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Netring.Meta.Lean

import Netring.CatHaikus
import Netring.NetringLinks

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open Netring

set_option pp.rawOnError true


#doc (Manual) "Bonjour" =>

%%%
authors := ["Sunrise"]
%%%

{index}[example]

![Polite cat](assets/stanley-dark.png)

Hello there fren


{include 1 Netring.CatHaikus}

{include 1 Netring.NetringLinks}


# Index
%%%
number := false
tag := "index"
%%%

{theIndex}

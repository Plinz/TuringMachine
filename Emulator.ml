(* Micha�l P�RIN, Verimag / Universit� Grenoble-Alpes, F�vrier 2017
 *
 * Part of the project TURING MACHINES FOR REAL
 *
 * (PROJECT 2019)  1. Multi-Bands Turing Machines working on a an alphabet A can be simulated by a single band Turing Machine using a augmented Alphbet A'
 *
 * (PROJECT 2017)  2. A Turing Machine using an alphabet A can be simulated by a Turing Machine using the binary alphabet {B,D}
 *
 * This module provides means to write Emulator for Problems 1 and 2.
 *
 *)



open Tricks
open State
open Action
open Transition
open Band
open Configuration
open Turing_Machine
open Execution
open Alphabet



type emulator   = State.t * Action.t * State.t -> Turing_Machine.t
type translator = Band.t list -> Band.t list

type simulator  =
    { name: string ;
      encoder: translator ;
      decoder: translator ;
      emulator: emulator
    }

type simulators = simulator list


module Simulator =
  (struct

    type loggers = Logger.t list

    let (fake_tm_named: string ->  Turing_Machine.t) = fun name ->
	  Turing_Machine.finalize name Turing_Machine.nop

    let (show_bands_using: loggers -> string -> Band.t list -> Band.t list) = fun loggers name bands ->
	  begin
 	    (Configuration.make (fake_tm_named name) bands) >> (Configuration.print_using loggers) ;
	    bands
	  end

    let rec (execute_action_using: simulators * loggers -> (State.t * Action.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (src,action,tgt) cfg ->
	  let cfg = cfg >> (Configuration.show_using loggers)
	  in
    let next_bands =
      match simulators with
      | [] -> Action.perform action cfg.bands

      | simulator :: other_simulators
        ->
        let e_tm    = simulator.emulator (src,action,tgt)
        and e_bands = (simulator.encoder  cfg.bands) >> (show_bands_using loggers (String.concat " to " [ "encoding" ; simulator.name ]))
        in let e_cfg = Configuration.make e_tm e_bands
        in
        let e_next_cfg = log_run_using (other_simulators,loggers) e_cfg
        in
			  let bands_updated_by_emulation = (simulator.decoder e_next_cfg.bands) >> (show_bands_using loggers (String.concat " " [ simulator.name ; "decoding"]))
			  in
        let bands_updated_by_execution = Action.perform action cfg.bands
        in
        if (* FIXME: Band.are_equivalents *) bands_updated_by_execution = bands_updated_by_emulation
			  then bands_updated_by_execution
			  else failwith
				  (String.concat " \n " [ "execute_action_using: simulation errors" ;
							Band.to_ascii_many bands_updated_by_emulation ;
							"are not equivalent to" ;
							Band.to_ascii_many bands_updated_by_execution ;
						      ])
	    in
      { cfg with bands = next_bands }


    and (execute_single_band_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Band.t -> Band.t) = fun (simulators,loggers) (src,instruction,tgt) band ->
	  let cfg = Configuration.make (fake_tm_named (Instruction.pretty instruction)) [band]
	  in let next_cfg = execute_instruction_using (simulators,loggers) (src,instruction,tgt) cfg
	  in List.hd next_cfg.bands

    and (execute_instruction_using: simulators * loggers -> (State.t * Instruction.t * State.t) -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
	  (match instruction with
	  | Run tm -> (* FIXME: ajoutez les transitions (source -nop-> init) et (accept -nop-> target) *)
		  run_using (simulators,loggers) (Configuration.make tm cfg.bands)

	  | Seq [] -> cfg
	  | Seq (inst::instructions) ->
		  let intermediate_state = State.fresh_from source in
		    cfg
		      >> (execute_instruction_using (simulators,loggers) (source, inst, intermediate_state))
		      >> (execute_instruction_using (simulators,loggers) (intermediate_state, Seq instructions, target))

	  | Parallel instructions ->
		  let next_bands =
		    List.map
		      (fun (inst,band) -> execute_single_band_instruction_using (simulators,loggers) (source,inst,target) band)
		      (Instruction.zip instructions cfg.bands)
		  in { cfg with bands = next_bands }

	  | Action action -> execute_action_using (simulators,loggers) (source,action,target) cfg
	  )

    and (execute_transition_using: simulators * loggers -> Transition.t -> Configuration.t -> Configuration.t) = fun (simulators,loggers) (source,instruction,target) cfg ->
	  let next_cfg = execute_instruction_using (simulators,loggers) (source,instruction,target) cfg
	  in { next_cfg with state = target}

    and (run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
	  match Execution.select_enabled_transition cfg.tm cfg with
	  | None -> cfg
	  | Some transition ->
		  let next_cfg = execute_transition_using (simulators,loggers) transition cfg
		  in run_using (simulators,loggers) next_cfg

    and (log_run_using: simulators * loggers -> Configuration.t -> Configuration.t) = fun (simulators,loggers) cfg ->
	  let loggers = cfg.logger :: loggers
	  in
	    let final_cfg = (run_using (simulators,loggers) cfg) >> (Configuration.show_using loggers)
	    in
	      begin
		cfg.logger#close ;
		final_cfg
	      end

  end)


open State
open Symbol
open Pattern
open Action
open Band
open Transition
open Turing_Machine

(* An example of a useless but correct translation that splits the effect of a transition into three steps

   (q) -- l / e : d --> (q')
   ===
   (q) -- l : H --> (q.0) -- ANY / e : H --> (q.00) -- ANY : d --> (q')
*)


module Split =
  (struct

    (* TRANSLATION OF BANDS *)

    let (encode: translator) = fun x -> x

    (* REVERSE TRANSLATION *)

    let (decode: translator) = fun x -> x

    (* EMULATION OF TRANSITIONS *)

    let (just_read: reading -> Action.t) = fun reading ->
	  RWM (reading, No_Write, Here)

    let (just_write: writing -> Action.t) = fun writing ->
	  match writing with
	  | No_Write     -> Nop
	  | Write symbol -> RWM (Match(ANY), Write symbol, Here)

    let (just_move: moving -> Action.t) = fun moving ->
	  RWM (Match(ANY), No_Write, moving)

    let (synchronize: Action.t list -> Instruction.t) = fun actionS ->
	  let rec (rec_synchronize: ('r list * 'w list * 'm list) -> Action.t list -> ('r list * 'w list * 'm list)) = fun (reads,writes,moves) actions ->
		match actions with
		| [] -> (List.rev reads, List.rev writes, List.rev moves)
		| action::actions ->
			(match action with
			| Nop        -> rec_synchronize ( Nop::reads , Nop::writes , Nop::moves) actions
			| RWM(r,w,m) -> rec_synchronize ( (just_read r)::reads , (just_write w)::writes , (just_move m)::moves) actions
			| Simultaneous _ -> failwith "Emulator.Split.synchronize: nested Simultaneous"
			)
	  in
	    let (reads,writes,moves) = rec_synchronize ([],[],[]) actionS
	    in
	      Seq[ Action(Simultaneous(reads)) ; Action(Simultaneous(writes)) ; Action(Simultaneous(moves)) ]

    let rec (transitions_emulating: State.t * Action.t * State.t -> Transition.t list) = fun (source,action,target) ->
	    (match action with
	    | Nop -> [ (source, Action(Nop), target) ]

	    | RWM(r,w,m) -> [ (source, Seq[ Action(just_read r) ; Action(just_write w) ; Action(just_move m) ], target) ]

	    | Simultaneous actions -> [ (source, synchronize actions, target) ]
	    )

    and (emulate_action: emulator) = fun (source,action,target) ->
	  let (source,target) =
	    if source <> target   (* /!\ loop in the emulated TM if source-target *)
	    then (source,target)
	    else (State.initial, State.accept)
	  in
	    let transitions =  transitions_emulating (source,action,target) in
	      { Turing_Machine.nop with
		name = String.concat "" [ "Split" ; Pretty.parentheses (Transition.to_ascii (source,Action action, target)) ] ;
		initial = source ;
		accept  = target ;
		transitions = transitions
	      }

    (* THE SIMULATOR *)

    let (* USER *) (simulator: simulator) = { name = "Split" ; encoder = encode ;  decoder = decode ; emulator = emulate_action }

  end)




module Binary =
  (struct

    (* TRANSLATION OF BANDS *)
    (* The modules Bit and Bits are defined in Alphabet.ml *)

    type encoding = (Symbol.t * Bits.t) list

    let (encode_on_one_band: encoding -> Band.t -> Band.t) = fun encoding band ->
      let rec foldi i f acc =
          if i <= 0 then acc else foldi (pred i) f (f acc) in
      let get_Tuple_From_Symbol encoding symbol =
          List.find (fun (s, _) -> s = symbol) encoding in
      let second_Element_Tuple (a,b) = b in
      let rec write_Encoded_Symbol_List band lst =
          match lst with
          | [] -> band
          | h :: t -> write_Encoded_Symbol_List (Band.move_head_right (Band.write h band)) t in
      let rec write_Non_Encoded_Symbol_List encoding band lst =
          match lst with
          | [] -> band
          | head :: tail -> write_Non_Encoded_Symbol_List encoding (write_Encoded_Symbol_List band (second_Element_Tuple (get_Tuple_From_Symbol encoding head))) tail in

      let alphabet = Alphabet.binary in
      let bandBinary = Band.make alphabet [] in
      let bandBinary = write_Encoded_Symbol_List bandBinary (second_Element_Tuple (get_Tuple_From_Symbol encoding band.head)) in
      let bandBinary = write_Non_Encoded_Symbol_List encoding bandBinary band.right in

      let () = Printf.printf "\nHEAD AND RIGHT\n" in
      let () = List.iter (fun e -> Printf.printf "%s " (Symbol.to_ascii e)) (List.rev bandBinary.left) in
      let () = Printf.printf "'%s' " (Symbol.to_ascii bandBinary.head) in
      let () = List.iter (fun e -> Printf.printf "%s " (Symbol.to_ascii e)) bandBinary.right in

      let () = Printf.printf "\nFolding AND LEFT \n" in
      let bandBinary = foldi ((((List.length band.right + List.length band.left) + 1) * band.alphabet.symbol_size_in_bits)) Band.move_head_left bandBinary in
      let bandBinary = write_Non_Encoded_Symbol_List encoding bandBinary (List.rev band.left) in
      let () = List.iter (fun e -> Printf.printf "%s " (Symbol.to_ascii e)) (List.rev bandBinary.left) in
      let () = Printf.printf "'%s' " (Symbol.to_ascii bandBinary.head) in
      let () = List.iter (fun e -> Printf.printf "%s " (Symbol.to_ascii e)) bandBinary.right in

      bandBinary


    let build_encoding : Alphabet.t -> encoding = fun alphabet ->
        let (d2b1_helper : int -> Symbol.t list) = fun x ->
          match x with
          | 0 -> [Bit.zero]
          | 1 -> [Bit.unit] in
        let rec d2b1 x y tab =
          match x with 0 ->
          if (List.length tab = y) then tab else (d2b1 0 y (tab@[Bit.zero]))
          | _ -> d2b1 (x/2) y (tab@(d2b1_helper (x mod 2))) in
        let symbol_to_bits : int -> int -> Bits.t
          = fun index size -> d2b1 index size []
        in
        List.mapi (fun index symbol -> (symbol, symbol_to_bits index alphabet.symbol_size_in_bits)) alphabet.symbols

    let encode_with : encoding -> Band.t list -> Band.t list = fun encoding bands ->
        List.map(fun band -> encode_on_one_band encoding band) bands

    (* REVERSE TRANSLATION *)

    let decode_with : encoding -> Band.t list -> Band.t list
      = fun encoding ->
        (fun bands -> bands)


    (* EMULATION OF TRANSITIONS *)

    let (emulate_action: State.t * Action.t * State.t -> Turing_Machine.t) = fun (source,action,target) ->

      (* PROJET 2017: modifiez ce code -> *)
	  { Turing_Machine.nop with
	    name = String.concat "" [ "Binary" ; Pretty.parentheses (Action.to_ascii action) ] ;
	    initial = State.initial ;
	    accept  = State.accept ;
	    transitions = [(State.initial,Action(action),State.accept)]
	  }


    (* THE SIMULATOR *)
    let make_simulator : Alphabet.t -> simulator
      = fun alphabet ->
        let encoding = build_encoding alphabet in
        { name = "Binary" ;
          encoder = encode_with encoding ;
          decoder = decode_with encoding ;
          emulator = emulate_action
        }
  end)


(* DEMO *)

open Alphabet

let (demo: unit -> unit) = fun () ->
      print_string "\n\n* DEMO * Emulator.ml:\n" ;
      let alphabet = Alphabet.make [B;Z;U] in
	let band = Band.make alphabet [U;U;Z;U] in
	  let tm = Turing_Machine.incr in
	    let cfg = Configuration.make tm [ band ] in
	      let _final_cfg = Simulator.log_run_using ([ (* Split.simulator ; *) Binary.make_simulator alphabet ],[]) cfg
		  in ()

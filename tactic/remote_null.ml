(*
 * This is a null-implementation of the
 * remote server.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

module Remote =
struct
   (************************************************************************
    * TYPES                                                                *
    ************************************************************************)

   (*
    * These are the possible responses to
    * a job.  The RemoteCanceled may be returned
    * if the job was canceled, but it is not required.
    * If the job was not canceled, the Cancel event is
    * never returned.
    *)
   type 'b response =
      RemoteCanceled
    | RemoteSuccess of 'b

   (*
    * A handle has a job argument,
    * and a cell for returning the value.
    *)
   type ('a, 'b) handle =
      { hand_arg : 'a;
        mutable hand_value : 'b response option
      }

   (*
    * Local jobs that are being served by the
    * local server.  We keep the handle that
    * references the job.
    *)
   type ('a, 'b) local = ('a, 'b) handle

   (*
    * An event has a polling function that returns
    * one of three values:
    *    EventSuccess x: got a value from the event
    *    EventFailure: no value is available.
    *    EventBlock event: a thread event to block on
    *)
   type 'a poll_value =
      PollSuccess of 'a
    | PollEvent of 'a Thread_event.event
    | PollFailure

   type 'a event = unit -> 'a poll_value

   (*
    * The main job keeps a queue of the submitted jobs.
    * Invariant:
    *    Either the requests are empty,
    *    or the pending queue is empty.
    *
    * queue_pending : a list of the jobs the client has submitted
    * queue_local : a list of the jobs running on the local client
    *)
   type ('a, 'b) t =
      { mutable queue_pending : ('a, 'b) handle list;
        mutable queue_local : ('a, 'b) local list
      }

   (************************************************************************
    * UTILITIES                                                            *
    ************************************************************************)

   (*
    * Remove a job from the local queue if it exists.
    *)
   let try_remove_local queue local =
      let rec remove = function
         local' :: locals ->
            if local' == local then
               locals
            else
               local' :: remove locals
       | [] ->
            []
      in
         queue.queue_local <- remove queue.queue_local

   (************************************************************************
    * IMPLEMENTATION                                                       *
    ************************************************************************)

   (*
    * Create a new empty queue.
    *)
   let create () =
      { queue_pending = [];
        queue_local = []
      }

   (*
    * Submit a new job.  Just create a handle and queue the job.
    *)
   let submit queue arg =
      let hand =
         { hand_arg = arg;
           hand_value = None
         }
      in
         queue.queue_pending <- hand :: queue.queue_pending;
         hand

   (*
    * Get the receive event for the handle.
    *)
   let event_of_handle queue hand () =
      match hand.hand_value with
         Some (RemoteSuccess x) ->
            PollSuccess x
       | _ ->
            PollFailure

   (*
    * Cancel a submitted event.
    * If this handle is being served by a local job,
    * cancel the local job.
    *)
   let cancel_handle queue hand =
      hand.hand_value <- Some RemoteCanceled;
      try_remove_local queue hand;
      queue.queue_pending <- List_util.removeq hand queue.queue_pending

   (*
    * When polled, the request event will try to pop a pending
    * job for local service.
    *)
   let request queue () =
      match queue.queue_pending with
         hand :: handles ->
            queue.queue_pending <- handles;
            queue.queue_local <- hand :: queue.queue_local;
            PollSuccess hand
       | [] ->
            PollFailure

   (*
    * Poll the local event.
    *)
   let event_of_local queue hand () =
      match hand.hand_value with
         Some x ->
            PollSuccess x
       | None ->
            PollFailure

   (*
    * Cancel a local job.
    * This may restart the handle.
    *)
   let cancel_local queue hand =
      match hand.hand_value with
         Some _ ->
            (* Local handle is complete *)
            ()

       | None ->
            (* Restart the handle *)
            queue.queue_pending <- hand :: queue.queue_pending

   (*
    * Return a value for the local job.
    *)
   let return_local queue hand x =
      hand.hand_value <- Some (RemoteSuccess x)

   (************************************************************************
    * SCHEDULING                                                           *
    ************************************************************************)

   (*
    * Wrap a function around an event.
    *)
   let wrap poll f () =
                      match poll () with
                         PollSuccess x ->
                            PollSuccess (f x)
                       | PollFailure ->
                            PollFailure
                       | PollEvent event ->
                            PollEvent (Thread_event.wrap event f)

   (*
    * Wrap a system event.
    *)
   let wrap_event event () =
      PollEvent event

   (*
    * During a select, poll all the events.
    * Collect the system events and block on them if no polls
    * are successful.
    *)
   let select events =
      let rec poll block_events = function
         event :: events ->
            begin
               match event () with
                  PollSuccess x ->
                     x
                | PollFailure ->
                     poll block_events events
                | PollEvent event ->
                     poll (event :: block_events) events
            end
       | [] ->
            Thread_event.select 0 block_events
      in
         poll [] events
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)

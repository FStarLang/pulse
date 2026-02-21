module PulseTutorial.Algorithms.Client
open PulseTutorial.Algorithms
open PulseTutorial.Algorithms.Client.Print
open Pulse
#lang-pulse

fn main ()
  returns exit: Int32.t
{
  let mut votes = [| 0ul; 4sz |];
  votes.(0sz) <- 1ul;
  votes.(1sz) <- 1ul;
  votes.(2sz) <- 0ul;
  votes.(3sz) <- 1ul;
  match majority votes 4sz {
    None -> {
      puts "No majority\n";
      0l;
    }
    Some v -> {
      printf "Majority: %d\n" v;
      0l;
    }
  }
}
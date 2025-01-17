open Unix

let rec compose_destructive = function
| [] -> failwith "unable to compose empty arguments"
| [(prog, prog_args)] ->
  execvp prog (Array.of_list (prog::prog_args))
| ((prog, prog_args) :: progs) -> 
  let (pipe_read, pipe_write) = pipe () in
  match fork () with
  | 0 ->
    dup2 pipe_write stdout;
    close pipe_read;
    execvp prog (Array.of_list (prog :: prog_args))
  | _ ->
    dup2 pipe_read stdin;
    close pipe_write;
    compose_destructive progs

let compose progs =
  match fork () with
  | 0 ->
    compose_destructive progs
  | pid ->
    let _ = waitpid [] pid in
    ()

let compose_in progs : in_channel =
  let pipe_read, pipe_write = pipe () in
  match fork () with
  | 0 ->
    dup2 pipe_write stdout;
    close pipe_read;
    compose_destructive progs
  | _ ->
    close pipe_write;
    in_channel_of_descr pipe_read

let compose_out progs : out_channel * int =
  let pipe_read, pipe_write = pipe () in
  match fork () with
  | 0 ->
    dup2 pipe_read stdin;
    close pipe_write;
    compose_destructive progs
  | pid ->
    close pipe_read;
    out_channel_of_descr pipe_write, pid

let compose_out_with progs f : unit =
  let out_chan, pid = compose_out progs in
  f out_chan;
  Out_channel.close out_chan;
  let _ = waitpid [] pid in
  ()


let compose_in_out progs f =
  let in_pipe_read, in_pipe_write = pipe () in
  let out_pipe_read, out_pipe_write = pipe () in
  match fork () with
  | 0 ->
    dup2 out_pipe_read stdin;
    dup2 in_pipe_write stdout;
    close out_pipe_write;
    close in_pipe_read;
    compose_destructive progs
  | pid ->
    close out_pipe_read;
    close in_pipe_write;
    match fork () with
    | 0 ->
      close in_pipe_read;
      let out_chan = out_channel_of_descr out_pipe_write in
      f out_chan;
      Out_channel.close out_chan;
      exit 0
    | _ ->
      close out_pipe_write;
      in_channel_of_descr in_pipe_read

module DL = Datalog_caml_interface

module Datalog = struct
  let backend = DL.Logic.DB.create
  let pairs = ()
end

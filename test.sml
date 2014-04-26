CM.make "sources.cm";

PrintAbsyn.print(TextIO.openOut "output.txt" , Parse.parse ("test2.tig"));


OS.Process.exit(OS.Process.success);

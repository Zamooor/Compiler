CM.make "sources.cm";

Semant.transProg(Parse.parse("test.tig"));
PrintAbsyn.print(TextIO.stdOut , Parse.parse ("test.tig"));

OS.Process.exit(OS.Process.success);

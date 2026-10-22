import Census.CertificateReaderTests

def main (args : List String) : IO UInt32 :=
  Census.CertificateReader.Tests.run args

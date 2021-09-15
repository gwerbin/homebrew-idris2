class Idris2 < Formula
  desc "Pure functional programming language with dependent types"
  homepage "https://www.idris-lang.org/"
  url "https://github.com/idris-lang/Idris2/archive/v0.4.0.tar.gz"
  sha256 "e06fb4f59838ca9da286ae3aecfeeeacb8e85afeb2e2136b4b751e06325f95fe"
  license "BSD-3-Clause"
  revision 2
  head "https://github.com/idris-lang/Idris2.git"

  bottle do
    sha256 cellar: :any,                 big_sur:      "3beffca58897ca836c87544b2a4a1096e70cb0e74e50a1a8b43f6aa4c3a41b75"
    sha256 cellar: :any,                 catalina:     "ad0955e64d0e51cb847765addaf6d850167a9a0edb25323a6446797a55ba4a4a"
    sha256 cellar: :any,                 mojave:       "13c5484d58c87098bb63ee6f861eae120d55b41b43764fae0a07c383658aaf96"
    sha256 cellar: :any_skip_relocation, x86_64_linux: "1eed0bfe631249c078c0ecee22e086d71a07d2b6c12b359e17ae47556a3e0386"
  end

  depends_on "coreutils" => :build
  depends_on "gmp" => :build
  depends_on "chezscheme"
  depends_on "coreutils"
  on_macos do
    # Zsh is not used at all in the build processes for platforms other than
    # Mac. Zsh is provided by MacOS on Mojave and later systems. This section
    # is in lieu of the `uses_from_macos` which isn't supported in the
    # `on_macos` block.
    depends_on "zsh" => :build if MacOS.version < :mojave
  end

  def install
    ENV.deparallelize
    scheme = Formula["chezscheme"].bin/"chez"

    # Stage 1: Bootstrap an up-to-date compiler, in a temporary location.
    mkdir "#{buildpath}/stage1"
    system "make", "bootstrap", "SCHEME=#{scheme}", "PREFIX=#{buildpath}/stage1"
    system "make", "install", "PREFIX=#{buildpath}/stage1"

    # Stage 2: Rebuild everything with the new compiler from Stage 1.
    # This is necessary for Idris2-LSP, and probably other software.
    system "make", "clean"
    system "make", "all", "IDRIS2_BOOT=#{buildpath}/stage1/bin/idris2", "PREFIX=#{libexec}"
    system "make", "install", "PREFIX=#{libexec}"
    system "make", "install-with-src-api"
    system "make", "install-with-src-libs"

    bin.install_symlink libexec/"bin/idris2"
    lib.install_symlink Dir["#{libexec}/lib/#{shared_library("*")}"]

    # Install shell completions
    (bash_completion/"idris2").write Utils.safe_popen_read(bin/"idris2", "--bash-completion-script", "idris2")
  end

  test do
    (testpath/"hello.idr").write <<~EOS
      module Main
      main : IO ()
      main =
        let myBigNumber = (the Integer 18446744073709551615 + 1) in
        putStrLn $ "Hello, Homebrew! This is a big number: " ++ ( show $ myBigNumber )
    EOS

    system bin/"idris2", "hello.idr", "-o", "hello"
    assert_equal "Hello, Homebrew! This is a big number: 18446744073709551616",
                 shell_output("./build/exec/hello").chomp
  end
end

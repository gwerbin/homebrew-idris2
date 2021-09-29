class Idris2 < Formula
  desc "Pure functional programming language with dependent types"
  homepage "https://www.idris-lang.org/"
  url "https://github.com/idris-lang/Idris2/archive/v0.5.1.tar.gz"
  sha256 "da44154f6eba5e22ec5ac64c6ba2c28d2df0a57cf620c5b00c11adb51dbda399"
  license "BSD-3-Clause"
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

    # Stage 1: Bootstrap an up-to-date compiler, in a temporary location.
    scheme_exe = Formula["chezscheme"].bin/"chez"
    stage1_dir = "#{buildpath}/stage1"
    mkdir stage1_dir
    system "make", "bootstrap", "SCHEME=#{scheme_exe}", "PREFIX=#{stage1_dir}"
    system "make", "install", "PREFIX=#{stage1_dir}"

    # Stage 2: Rebuild everything with the new compiler from Stage 1, including the Idris 2 API package.
    # This is necessary for Idris2-LSP, and probably other software.
    make_overrides = ["IDRIS2_BOOT=#{stage1_dir}/bin/idris2", "PREFIX=#{libexec}"]
    system "make", "clean"
    system "make", "all", *make_overrides
    system "make", "install", *make_overrides
    system "make", "install-api", *make_overrides
    system "make", "install-libs", *make_overrides
    system "make", "install-with-src-api", *make_overrides
    system "make", "install-with-src-libs", *make_overrides
    system "make", "install-libdocs", *make_overrides

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

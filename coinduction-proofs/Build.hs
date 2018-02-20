import Prelude
    ( (++),
      ($),
      Eq((/=), (==)),
      Monad((>>), return),
      Foldable(null),
      Maybe(Just),
      IO,
      Either(Right),
      FilePath,
      String,
      not,
      readFile,
      take,
      reverse,
      error,
      (.),
      lines,
      maybe )
import Control.Monad ( unless )
import Data.Maybe ( listToMaybe )
import System.Directory ( getCurrentDirectory )
import System.Console.GetOpt ( OptDescr(Option), ArgDescr(ReqArg) )
import Development.Shake
    ( ShakeOptions(shakeChange, shakeThreads),
      Change(ChangeModtimeAndDigestInput),
      Rules,
      Stdout(Stdout),
      Stderr(Stderr),
      liftIO,
      shakeOptions,
      alwaysRerun,
      orderOnly,
      want,
      phony,
      need,
      removeFiles,
      writeFileChanged,
      withoutActions,
      cmd,
      shakeArgsWith,
      (*>) )
import Development.Shake.FilePath
    ( makeRelative,
      normalise,
      takeDirectory,
      takeDirectory1,
      dropDirectory1,
      takeExtension,
      dropFileName,
      dropExtension,
      (</>),
      (-<.>) )
import Development.Shake.Util ( needMakefileDependencies )

{- This program is a shake-based buildsystem for our Coq files.
   It should be run through build.sh rather than directly.

   It's very quick to dectect which files are already up to date
   (under 1 second for a null build from the root directory),
   and compiles only minimal necessary dependencies
   (as calculated by coq_dep, and as opposed to a recursive make
   always needing to build everything in common/ ).

   An include path suitable for the current directory structure
   is automatically calculated (by the "includes" function),
   and a simple system of specifying groups of files with "Files.mk"
   files is provided..

   Positional arguments to build.sh are taken as targets.
   With no targets, the default is to build the Files.mk file
   in the directory where build.sh was run.

   A target file with the .vo extension is built if necessary
   by compiling the corresponding .v file.

   A file named Files.mk is "built", without ever considering it
   "up to date" by recursively requesting all of paths listed
   (one per line) in that file, after replacing any .v extensions
   with .vo for convenience. Relative paths are interpreted
   relative to the directory containing the Files.mk file.
   Generally Files.mk files list only .v files and some Files.mk
   files from subdirectories.

   The dependency information for $dir/file.v
   is stored in .shake/$dir/file.v.d.
 -}

shakeArgsRel :: ShakeOptions -> (FilePath -> Rules ()) -> IO ()
shakeArgsRel opts rules =
  shakeArgsWith opts 
  [Option "R" ["relative-to"] (ReqArg Right "PATH")
         "base path for interpreting relative target names"] $ \relTo targets0 -> do
  pwd <- getCurrentDirectory
  let basePath = maybe "." (makeRelative pwd . normalise)
                   (listToMaybe $ reverse relTo)
      targets = [makeRelative pwd (basePath </> normalise t) | t <- targets0]
  return $ Just $ if null targets
                  then rules basePath
                  else want targets >> withoutActions (rules basePath)

main :: IO ()
main = shakeArgsRel shakeOptions{shakeThreads=8, shakeChange=ChangeModtimeAndDigestInput} $ \relDir -> do
    want [relDir </> "Files.mk"]

    "//Files.mk" *> \out -> do
      alwaysRerun
      let base = dropFileName out
      let target f = if takeExtension f == ".v" then f -<.> ".vo" else f
      content <- liftIO $ readFile out
      need [base </> target line | line <- lines content, not (null line), take 1 line /= "#"]

    phony "distclean" $ do
      liftIO $ removeFiles "." ["//*.vo","//*.glob","//*.v.d"]

    "//*.vo" *> \out -> do
      let depfile = ".shake" </> out -<.> ".v.d"
      orderOnly [depfile]
      needMakefileDependencies depfile
      cmd "coqc" (includes out) [out -<.> ".v"]

    ".shake//*.v.d" *> \out -> do
      let vfile = dropDirectory1 (dropExtension out)
      need [vfile]
      (Stdout stdout,Stderr err) <- cmd "coqdep" (includes vfile) vfile
      unless (null err) $ error ("Error generating dependencies: "++err)
      let dropDots ('.':'/':r) = dropDots r
          dropDots (c:r) = c:dropDots r
          dropDots [] = []
      writeFileChanged out (dropDots stdout)

includes :: String -> [String]
includes out =
  ["-I",takeDirectory out
  ,"-I",takeDirectory1 out
  ,"-I","common"]

{-# LANGUAGE OverloadedStrings#-}

module Main (main) where

import Control.Concurrent (threadDelay)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import System.Process (withCreateProcess, proc)
import Test.Sandwich
import Test.Sandwich.WebDriver
import Test.WebDriver

spec :: TopSpec
spec = introduceWebDriver wdOptions $
  it "MuddyChildren examples gives expected output in web interface" $ withSession1 $ do
    openPage "http://127.0.0.1:3000/index.html"
    findElem (ByCSS "input[value='MuddyChildren']") >>= click
    findElem (ByCSS "#runbutton") >>= click
    liftIO $ putStrLn "clicked run and waitng 4 second for MathJax"
    liftIO $ threadDelay 4000000
    liftIO $ putStrLn "continuing"
    output <- getText =<< findElem (ByCSS "#output")
    output `textShouldContain` "Oalice={p2,p3}"
    output `textShouldContain` expectedMcOutput

expectedMcOutput :: Text
expectedMcOutput = "At which states is\n⟨!⋁{p1,p2,p3}⟩⋁{Kalice?p1,Kbob?p2,Kcarol?p3}\ntrue?\n{p1},{p2},{p3}\n"

wdOptions :: WdOptions
wdOptions = (defaultWdOptions "/tmp/tools") {
  capabilities = firefoxCapabilities
  , runMode = RunHeadless defaultHeadlessConfig
  }

main :: IO ()
main = do
  putStrLn "starting smcdel-web before running tests"
  withCreateProcess (proc "stack" ["exec", "smcdel-web"]) $
    \_ _ _ _ -> do
      (_, numFailures) <- runSandwich' Nothing defaultOptions spec
      when (numFailures > 0) $ error $ show numFailures ++ " tests failed"

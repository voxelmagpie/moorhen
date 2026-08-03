{-# LANGUAGE TemplateHaskell #-}

module Embed where

import Data.FileEmbed
import Data.Text (Text)

helpFile :: Text
helpFile = $(embedStringFile "help.txt")

builtinsMjs :: Text
builtinsMjs = $(embedStringFile "builtins.mjs")

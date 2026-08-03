## About

Work-in-progress language with 
* Imperative control flow
* Immutable data
* Mutable local variables
* Effects tracking
* Referential transparency

## Compiler development environment setup (Linux)

```shell

sudo apt install git nodejs time

# Install GHCup from https://www.haskell.org/ghcup/

curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_GHC_VERSION=9.10.3 sh
```

Pick the default for all options and don't install HLS if using VSCodium/VSCode as
the extension will download the correct version


## Licence

Copyright (c) 2026 "VoxelMagpie"

This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at https://mozilla.org/MPL/2.0/.

The MPL-2.0 licence applies to every file, regardless of whether it has a licence header or not.

The MPL-2.0 is similar to the LGPL but without the need for dynamic linking. 

This means that any changes made to the code must be shared under the same licence
but the code can be used unmodified within a proprietary/GPL/MIT/etc. codebase. 

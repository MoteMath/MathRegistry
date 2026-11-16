& {
    $ErrorActionPreference = 'Stop'
    $pythonCommand = $null
    $pythonArgs = @()
    foreach ($candidate in @('py', 'python', 'python3')) {
        if (Get-Command $candidate -ErrorAction SilentlyContinue) {
            $candidateArgs = @()
            if ($candidate -eq 'py') { $candidateArgs = @('-3') }
            & $candidate @candidateArgs -c 'import sys; sys.exit(sys.version_info < (3, 10))' 2>$null
            if ($LASTEXITCODE -eq 0) {
                $pythonCommand = $candidate
                $pythonArgs = $candidateArgs
                break
            }
        }
    }
    if (-not $pythonCommand) { throw 'mreg needs Python 3.10 or newer. Install Python and run this command again.' }
    $baseUrl = 'https://mathregistry.com'
    if ($env:MREG_INSTALL_BASE_URL) { $baseUrl = $env:MREG_INSTALL_BASE_URL.TrimEnd('/') }
    $installerFile = [System.IO.Path]::GetTempFileName()
    try {
        Invoke-WebRequest -UseBasicParsing -Uri "$baseUrl/downloads/install.py" -OutFile $installerFile
        & $pythonCommand @pythonArgs $installerFile --base-url $baseUrl
        if ($LASTEXITCODE -ne 0) { throw 'mreg installation failed. See the message above.' }
        if ($env:MREG_NO_MODIFY_PATH -ne '1') {
            $binDir = Join-Path $env:USERPROFILE '.local\bin'
            if ($env:MREG_BIN_DIR) { $binDir = $env:MREG_BIN_DIR }
            $env:Path = $binDir + ';' + $env:Path
        }
    } finally {
        Remove-Item -LiteralPath $installerFile -Force
    }
}

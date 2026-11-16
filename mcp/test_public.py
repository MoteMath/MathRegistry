"""Self-contained tests for the public MCP protocol entry point."""
import json
import unittest

import server


class EmptyIndex:
    def fork(self):
        return self


class ProtocolTests(unittest.TestCase):
    def request(self, method, **extra):
        payload = {"jsonrpc": "2.0", "id": 1, "method": method, **extra}
        return json.loads(server.handle(json.dumps(payload), EmptyIndex()))

    def test_initialize(self):
        result = self.request("initialize", params={"protocolVersion": "2025-03-26"})
        self.assertEqual(result["result"]["serverInfo"]["name"], "mathregistry-tools-local")

    def test_tools_list_uses_shipped_contract(self):
        result = self.request("tools/list")
        self.assertGreater(len(result["result"]["tools"]), 0)

    def test_bad_json(self):
        result = json.loads(server.handle("{", EmptyIndex()))
        self.assertEqual(result["error"]["code"], -32700)

    def test_unknown_tool(self):
        result = self.request("tools/call", params={"name": "missing", "arguments": {}})
        self.assertEqual(result["error"]["code"], -32602)


if __name__ == "__main__":
    unittest.main()

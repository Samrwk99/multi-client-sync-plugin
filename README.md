### Multi Client Sync Plugin
# You need both the plugin and extension for this to work
This project contains both a Sillytavern plugin and extension that sync up multiple tabs open connected to the same Sillytavern instance.
It supports chat streaming, avoids having the same chat overwritten by another tab's usage and has the option to stop generations in another tab.


# Install and Set Up the Plugin

1. Navigate to your SillyTavern directory.
2. Open `config.yaml`.
3. Set `enableServerPlugins` to `true`:

```yaml
enableServerPlugins: true
```

4. Open the `plugins` directory.
5. From this directory, run:

```bash
git clone https://github.com/Samrwk99/multi-client-sync-plugin.git
```

6. Restart SillyTavern.

# Get the extension

You can get the extension here: [Multi Client Sync Extension](https://github.com/Samrwk99/multi-client-sync-extension)

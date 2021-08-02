/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.dubbo.remoting.transport.netty4;

import org.apache.dubbo.common.URL;
import org.apache.dubbo.common.extension.ExtensionLoader;
import org.apache.dubbo.common.logger.Logger;
import org.apache.dubbo.common.logger.LoggerFactory;
import org.apache.dubbo.config.SslConfig;
import org.apache.dubbo.remoting.transport.security.SecurityProvider;
import org.apache.dubbo.rpc.model.ApplicationModel;

import io.netty.handler.ssl.ClientAuth;
import io.netty.handler.ssl.OpenSsl;
import io.netty.handler.ssl.SslContext;
import io.netty.handler.ssl.SslContextBuilder;
import io.netty.handler.ssl.SslProvider;

import javax.net.ssl.SSLException;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.security.Provider;
import java.security.Security;


public class SslContexts {

    private static final Logger logger = LoggerFactory.getLogger(SslContexts.class);

    public static SslContext buildServerSslContext(URL url) {
        SslContextBuilder sslClientContextBuilder = null;

        try {
            InputStream serverKeyCertChainPathStream;
            InputStream serverPrivateKeyPathStream;
            InputStream serverTrustCertCollectionPathStream;
            String password = null;

            SslConfig sslConfig = getSslConfig();
            if (sslConfig != null && sslConfig.getServerKeyCertChainPath() != null) {
                serverKeyCertChainPathStream = sslConfig.getServerKeyCertChainPathStream();
                serverPrivateKeyPathStream = sslConfig.getServerPrivateKeyPathStream();
                serverTrustCertCollectionPathStream = sslConfig.getServerTrustCertCollectionPathStream();
                password = sslConfig.getServerKeyPassword();
            } else {
                SecurityProvider.CertPair certPair = ExtensionLoader.getExtensionLoader(SecurityProvider.class)
                    .getSupportedExtensionInstances()
                    .stream()
                    .filter(SecurityProvider::isSupported)
                    .map(SecurityProvider::request).findFirst().orElse(null);
                if (certPair != null) {
                    serverKeyCertChainPathStream = new ByteArrayInputStream(certPair.getPublicKey().getBytes(StandardCharsets.UTF_8));
                    serverPrivateKeyPathStream = new ByteArrayInputStream(certPair.getPrivateKey().getBytes(StandardCharsets.UTF_8));
                    serverTrustCertCollectionPathStream = new ByteArrayInputStream(certPair.getCaCert().getBytes(StandardCharsets.UTF_8));
                } else {
                    throw new IllegalStateException("Ssl enabled, but no ssl cert information provided!");
                }
            }

            if (password != null) {
                sslClientContextBuilder = SslContextBuilder.forServer(serverKeyCertChainPathStream,
                    serverPrivateKeyPathStream, password);
            } else {
                sslClientContextBuilder = SslContextBuilder.forServer(serverKeyCertChainPathStream,
                    serverPrivateKeyPathStream);
            }

            if (serverTrustCertCollectionPathStream != null) {
                sslClientContextBuilder.trustManager(serverTrustCertCollectionPathStream);
                sslClientContextBuilder.clientAuth(ClientAuth.REQUIRE);
            }

            serverKeyCertChainPathStream.close();
            serverPrivateKeyPathStream.close();
            serverTrustCertCollectionPathStream.close();
        } catch (Exception e) {
            throw new IllegalArgumentException("Could not find certificate file or the certificate is invalid.", e);
        }
        try {
            return sslClientContextBuilder.sslProvider(findSslProvider()).build();
        } catch (SSLException e) {
            throw new IllegalStateException("Build SslSession failed.", e);
        }

    }

    public static SslContext buildClientSslContext(URL url) {
        SslContextBuilder builder = SslContextBuilder.forClient();

        try {
            InputStream clientKeyCertChainPathStream;
            InputStream clientPrivateKeyPathStream;
            InputStream clientTrustCertCollectionPathStream;
            String password = null;

            SslConfig sslConfig = getSslConfig();
            if (sslConfig != null && sslConfig.getServerKeyCertChainPath() != null) {
                clientKeyCertChainPathStream = sslConfig.getClientKeyCertChainPathStream();
                clientPrivateKeyPathStream = sslConfig.getClientPrivateKeyPathStream();
                clientTrustCertCollectionPathStream = sslConfig.getClientTrustCertCollectionPathStream();
                password = sslConfig.getClientKeyPassword();
            } else {
                SecurityProvider.CertPair certPair = ExtensionLoader.getExtensionLoader(SecurityProvider.class)
                    .getSupportedExtensionInstances()
                    .stream()
                    .filter(SecurityProvider::isSupported)
                    .map(SecurityProvider::request).findFirst().orElse(null);
                if (certPair != null) {
                    clientKeyCertChainPathStream = new ByteArrayInputStream(certPair.getPublicKey().getBytes(StandardCharsets.UTF_8));
                    clientPrivateKeyPathStream = new ByteArrayInputStream(certPair.getPrivateKey().getBytes(StandardCharsets.UTF_8));
                    clientTrustCertCollectionPathStream = new ByteArrayInputStream(certPair.getCaCert().getBytes(StandardCharsets.UTF_8));
                } else {
                    throw new IllegalStateException("Ssl enabled, but no ssl cert information provided!");
                }
            }

            if (clientTrustCertCollectionPathStream != null) {
                builder.trustManager(clientTrustCertCollectionPathStream);
            }

            if (clientKeyCertChainPathStream != null && clientPrivateKeyPathStream != null) {
                if (password != null) {
                    builder.keyManager(clientKeyCertChainPathStream, clientPrivateKeyPathStream, password);
                } else {
                    builder.keyManager(clientKeyCertChainPathStream, clientPrivateKeyPathStream);
                }
            }
        } catch (Exception e) {
            throw new IllegalArgumentException("Could not find certificate file or find invalid certificate.", e);
        }
        try {
            return builder.sslProvider(findSslProvider()).build();
        } catch (SSLException e) {
            throw new IllegalStateException("Build SslSession failed.", e);
        }
    }

    private static SslConfig getSslConfig() {
        return ApplicationModel.getConfigManager().getSsl().orElse(null);
    }

    /**
     * Returns OpenSSL if available, otherwise returns the JDK provider.
     */
    private static SslProvider findSslProvider() {
        if (OpenSsl.isAvailable()) {
            logger.info("Using OPENSSL provider.");
            return SslProvider.OPENSSL;
        } else if (checkJdkProvider()) {
            logger.info("Using JDK provider.");
            return SslProvider.JDK;
        }
        throw new IllegalStateException(
            "Could not find any valid TLS provider, please check your dependency or deployment environment, " +
                "usually netty-tcnative, Conscrypt, or Jetty NPN/ALPN is needed.");
    }

    private static boolean checkJdkProvider() {
        Provider[] jdkProviders = Security.getProviders("SSLContext.TLS");
        return (jdkProviders != null && jdkProviders.length > 0);
    }

}
